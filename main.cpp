#include<bits/stdc++.h>

#define MOD 1000000007
#define pb push_back
#define mp make_pair
#define ff first
#define ss second

//#define DEBUG

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
ll ans=0;
vector<pii> steiner;
vi low, depth;
vvi bcc;
vector<set<int>> components;

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
            adj.resize(n+1),is_terminal.resize(n+1,0), removed.resize(n+1,  0),
            low.resize(n+1), depth.resize(n+1, 0),  bcc.resize(n+1, vi(n+1,0));
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
            if (g[i][*it] < weight[i][*it]) {
#ifdef DEBUG
                cout<<"Removing "<<i<<"-"<<*it<<endl;
#endif
                adj[*it].erase(i),it = adj[i].erase(it); 
            }
            else ++it;
}

void remove_non_terminals()
{
    for (int i=1; i<=n; ++i) {
        int j=i;
        while(not removed[j] and not is_terminal[j] and adj[j].size()==1) {
            auto p = *adj[j].begin();
            adj[p].erase(j);
            removed[j]=1;
#ifdef DEBUG
            cout<<"Removing "<<j<<endl;
#endif
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
#ifdef DEBUG
            cout<<"Removing "<<x<<endl;
#endif
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
    while (i != j) steiner.pb(mp(i,next_hop[i][j])), i=next_hop[i][j];
}

bool all_zeros(string& s)
{
    for (auto& i: s)
        if (i!='0') return false;
    return true;
}

void print_path(string s, int q,map<pair<string, int>, pair<int, pair<string, string>>>& tree)
{
    if (all_zeros(s)) return;
    int p = tree[mp(s,q)].ff;
    print_actual_path(q, p);
    string e = tree[mp(s,q)].ss.ff, f = tree[mp(s,q)].ss.ss;
    print_path(e, p, tree);
    print_path(f, p, tree);
}

void annotate_cut_vertex(int i, int p, int d, stack<pii>& s, int& count)
{
    depth[i]=d;
    low[i]=d;
    int c=0;
    for (auto& j: adj[i]) {
        if (depth[j]==0)  {
            s.push(mp(i,j));
            annotate_cut_vertex(j, i, d+1, s, count);
            low[i] = min(low[i], low[j]);
            if (low[j] >= d and p!=0 or p==0 and c>1) {
                ++count;
                int u, v;
                set<int> new_comp;
                do {
                    u=s.top().ff, v=s.top().ss;
                    bcc[u][v]=bcc[v][u]=count;
                    new_comp.insert(u), new_comp.insert(v);
                    s.pop();
                } while(mp(u,v) != mp(i,j));
                components.pb(new_comp);
            }
            ++c;
        }
        else if (j!=p and depth[j]<depth[i])
            low[i] = min(low[i], depth[j]),
            s.push(mp(i,j));
    }
}

int label_bccs(int root)
{
    stack<pii> s;
    int count=0;
    annotate_cut_vertex(root, 0, 1, s, count);
    if (not s.empty()) {
        ++count;
        set<int> new_comp;
        while (not s.empty()) {
            int u = s.top().ff, v = s.top().ss;
            bcc[u][v] = bcc[v][u] = count;
            new_comp.insert(u), new_comp.insert(v);
            s.pop();
        }
        components.pb(new_comp);
    }
    return count;
}

void add_terminals(int root)
{
    vi par(n+1, 0);
    queue<int> q;
    q.push(root);
    par[root]=root;
    while (not q.empty()) {
        int x = q.front();
        q.pop();
        for (auto& j: adj[x])
            if (par[j]==0) 
                par[j]=x, q.push(j);
    }
    for (int i=1; i<=n; ++i) {
        if (not is_terminal[i]) continue;
        int j=i, pre=i;
        while (par[j]!=j) {
            if (pre != j and bcc[j][par[j]] != bcc[j][pre]) is_terminal[j]=true;
            pre =      j;
            j   = par[j];
        }
    }
}

void solve(set<int>& vertices)
{
    vi term;
    for (auto& i: vertices)
        if(is_terminal[i]) term.pb(i);
    int q = term.back();
    int k = term.size();
    if (k<=1) return;
    if (k==2) {
        ans += g[term[0]][term[1]], print_actual_path(term[0],term[1]);
        return;
    }
    map<pair<string, int>, ll> dp;
    map<pair<string, int>, pair<int, pair<string, string>>> tree;
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
    ll val=inf;
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
        if (val > g[q][j]+u)
            val = g[q][j]+u, 
            tree[mp(C,q)] = mp(j, mp(e,f));
    }
    ans += val;
    print_path(C,q,tree);
}

int main(int argc, char** argv)
{
    ios::sync_with_stdio(false);
    input(cin);
    shortest_path();
    if (k<=1) 
        cout<<"VALUE 0\n";
    
    else { 
        preprocess();
        vi term;
        for (int i=1; i<=n; ++i) {
            if (is_terminal[i]) term.pb(i);
        }
        if (k==2) 
            cout<<"VALUE "<<g[term[0]][term[1]]<<"\n",
            print_actual_path(term[0], term[1]);
    
        else {
            int num_bccs = label_bccs(term[0]);
            add_terminals(term[0]);
            for (auto& vert: components)
                solve(vert);
            cout<<"VALUE "<<ans<<"\n";
        }
        for (auto& e: steiner)
            cout<<e.ff<<" "<<e.ss<<"\n";
    }
	return 0;
}
