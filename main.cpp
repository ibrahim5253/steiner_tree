#include<bits/stdc++.h>

#define MOD 1000000007
#define pb push_back
#define mp make_pair
#define ff first
#define ss second

using namespace std;

using ll=long long;
using ull=unsigned long long;
using pii=pair<int, int>;
using pll=pair<ll,ll>;
using vi=vector<int>;
using vll=vector<ll>;
using pill=pair<int,ll>;
using vvi=vector<vi>;

ll const inf = 1e10;

int n, m;
vector<vll> g;
vector<set<int>> adj;
vector<vll> weight;
vvi next_hop;
vi is_terminal;
vi removed;
int  k;
ll ans=inf;
map<pair<string, int>, ll> dp;
map<pair<string, int>, pair<int, pair<string, string>>> tree;

void input(istream& fin)
{
    string line;
    while (getline(fin, line)) {
        stringstream ss(line);
        string s;
        ss>>s;
        if (s=="SECTION" or s=="END") continue;
        if (s=="Nodes") 
            ss>>n, g.resize(n+1, vll(n+1, inf)), next_hop.resize(n+1, vi(n+1)), 
            adj.resize(n+1), is_terminal.resize(n+1,0), removed.resize(n+1, 0);
        if (s=="Edges") ss>>m;
        if (s=="E") {
            int u, v;ll w;ss>>u>>v>>w;
            adj[u].insert(v), adj[v].insert(u);
            g[u][v] = g[v][u] = min(g[u][v], w);
            next_hop[u][v] = v, next_hop[v][u] = u;
        }
        if (s=="Terminals") ss>>k;
        if (s=="T") {
            int t;ss>>t;
            is_terminal[t]=true;
        }
        if (s=="EOF") break;
    }
    for (int i=0; i<=n; ++i)
        g[i][i] = 0, next_hop[i][i] = i;
    weight=g;
}

void shortest_path()
{
    for (int k=1; k<=n; ++k)
        for (int i=1; i<=n; ++i)
            for (int j=1; j<=n; ++j)
                if (g[i][j] > g[i][k] + g[k][j])
                    g[i][j] = g[i][k] + g[k][j],
                    next_hop[i][j] = next_hop[i][k];
}

void remove_long_edge()
{
    for (int i=1; i<=n; ++i)
        for (auto it = adj[i].begin(); it != adj[i].end(); )
            if (g[i][*it] < weight[i][*it]) adj[*it].erase(i),it = adj[i].erase(it); 
            else ++it;
}

void remove_non_terminals()
{
    for (int i=1; i<=n; ++i) {
        int j=i;
        while(not removed[i] and not is_terminal[j] and adj[j].size()==1) {
            auto p = *adj[j].begin();
            adj[p].erase(j);
            removed[j]=1;
            j=p;
        }
    }
    for (int i=1; i<=n; ++i) {
        if (removed[i] or is_terminal[i] or adj[i].size()>2) continue;
        queue<int> q;
        q.push(i);
        set<int> vis;
        vis.insert(i);
        while (not q.empty()) {
            int x = q.front();
            q.pop();
            int u = *adj[x].begin();
            int v = *next(adj[x].begin());
            removed[x]=1;
            adj[u].erase(x), adj[v].erase(x);
            if (adj[u].find(v) == adj[u].end())
                adj[u].insert(v), adj[v].insert(u), 
                weight[u][v] = weight[v][u] = weight[x][u]+weight[x][v];
            if (not is_terminal[u] and adj[u].size() == 2 and not vis.count(u)) 
                q.push(u), vis.insert(u);
            if (not is_terminal[v] and adj[v].size() == 2 and not vis.count(v)) 
                q.push(v), vis.insert(v);
        }
    }
}

void preprocess()
{
    remove_long_edge();
    //cout<<"removed long edges.."<<endl;
    remove_non_terminals();
}

bool next_subset(string& s, string& t)
{
    int l = s.length();
    for (int i=l-1; i>=0; --i)  {
        if (t[i]=='0') continue;
        if (s[i]=='1') {
            s[i]='0';
            return true;
        }
        s[i]='1';
    }
    return false;
}

string complement(const string& s, const string& t)
{
    int l = s.length();
    string r = s;
    for (int i=0; i<l; ++i) {
        if (t[i]=='0') continue;
        r[i] = '0'+('1'-r[i]);
    }
    return r;
}

void print_actual_path(int i, int j)
{
    while (i != j) cout<<i<<" "<<next_hop[i][j]<<"\n", i=next_hop[i][j];
}

bool all_zeros(string& s)
{
    for (auto& i: s)
        if (i!='0') return false;
    return true;
}

void print_path(string s, int q)
{
    if (all_zeros(s)) return;
    int p = tree[mp(s,q)].ff;
    print_actual_path(q, p);
    string e = tree[mp(s,q)].ss.ff, f = tree[mp(s,q)].ss.ss;
    print_path(e, p);
    print_path(f, p);
}

void solve(vi& vertices, vi& term)
{
    int q = term.back();
    int k = term.size();
    term.pop_back();
    for (int i=0; i<term.size(); ++i) {
        string t(k-1, '0');
        t[i]='1';
        for (auto& j: vertices)
            dp[mp(t,j)] = g[term[i]][j],
            tree[mp(t, j)] = mp(term[i], mp(string(k-1,'0'), string(k-1, '0')));
    }
    for (int m=2; m<term.size(); ++m) {
        string D(k-1, '0'); 
        for (int i=k-1-m; i<k-1; ++i)
            D[i]='1';
        do {
            for (auto& i: vertices)
                dp[mp(D,i)]=inf;
            for (auto& j: vertices) {
                ll u=inf;
                int p = D.find('1');
                assert (p != string::npos);
                string S = D;
                S[p]='0';
                string E = D;
                string e, f;
                while (next_subset(E, S)) {
                    string Ec = complement(E, D);
                    if (u > dp[mp(E,j)] + dp[mp(Ec,j)])
                        u = dp[mp(E,j)] + dp[mp(Ec,j)], e=E, f=Ec;
                }
                for (auto& i: vertices)
                    if (dp[mp(D,i)] > g[i][j] + u)
                        dp[mp(D,i)] = g[i][j] + u,
                        tree[mp(D,i)] = mp(j, mp(e,f));
            }
        }while (next_permutation(D.begin(), D.end()));
    }
    string C(k-1, '1');
    for (auto& j: vertices) {
        ll u=inf;
        string E=C;
        string S=C;
        S[0]='0';
        string e, f;
        while (next_subset(E, S)) {
            string Ec = complement(E, C);
            if (u > dp[mp(E,j)] + dp[mp(Ec,j)])
                u = dp[mp(E,j)] + dp[mp(Ec,j)], e=E, f=Ec;
        }
        if (ans > g[q][j]+u)
            ans = g[q][j]+u, 
            tree[mp(C,q)] = mp(j, mp(e,f));
    }
    cout<<"VALUE "<<ans<<"\n";
    print_path(C,q);
}

int main(int argc, char** argv)
{
    ios::sync_with_stdio(false);
    input(cin);
    shortest_path();
    if (k<=1) 
        cout<<"VALUE 0\n";
    
    else{ 
        preprocess();
//        cout<<"preprocessing over.."<<endl;
        vi vert, term;
        for (int i=1; i<=n; ++i) {
            if (not removed[i]) vert.pb(i);
            if (is_terminal[i]) term.pb(i);
        }
        if (k==2) 
            cout<<"VALUE "<<g[term[0]][term[1]]<<"\n",
            print_actual_path(term[0], term[1]);
    
        else solve(vert, term);
    }
	return 0;
}
