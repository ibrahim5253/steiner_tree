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

class dsu {
    private:
        vi par, rank, csize;
        int nc=0;
    public:
        dsu(int n) : par(n), rank(n, 0), csize(n, 1), nc(n) {
            iota(par.begin(), par.end(), 0);
        }  
        int find_set(int x)
        {
            if (x != par[x])
                par[x] = find_set(par[x]);
            return par[x];
        }
        void union_(int x, int y) {link(find_set(x), find_set(y));}
        void link(int x, int y) {
            if (x==y) return;
            if (rank[x] > rank[y])
                par[y] = x, csize[x] += csize[y];
            else {
                par[x] = y, csize[y] += csize[x];
                if (rank[x] == rank[y])
                    ++rank[y];
            }
            --nc;
        }
        int comp_size(int x) {
            if (x != par[x])
                par[x] = find_set(par[x]);
            return csize[par[x]];
        }
        int num_comp() {return nc;}
};

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
set<int> active_vertices;
map<pii, vector<pii>> edge_map;

void input(istream& fin)
{
    string line;
    while (getline(fin, line)) {
        stringstream ss(line);
        string s;
        ss>>s;
        if (s=="SECTION" or s=="END") continue;
        if (s=="Nodes") {
            ss>>n, g.resize(n+1, vll(n+1, inf)), next_hop.resize(n+1, vi(n+1)), 
            adj.resize(n+1),is_terminal.resize(n+1,0), removed.resize(n+1,  0),
            low.resize(n+1), depth.resize(n+1, 0),  bcc.resize(n+1, vi(n+1,0)),
            weight.resize(n+1, vll(n+1, inf));

            for (int i=1; i<=n; ++i) active_vertices.insert(i);
        }
        if (s=="Edges") ss>>m;
        if (s=="E") {
            int u, v;ll w;ss>>u>>v>>w;
            if (u==v) continue;
            adj[u].insert(v), adj[v].insert(u);
            weight[u][v] = weight[v][u] = min(weight[u][v],w);
        }
        if (s=="Terminals") ss>>k;
        if (s=="T") {
            int t;ss>>t;
            is_terminal[t]=true;
        }
        if (s=="EOF") break;
    }
    for (int i=0; i<=n; ++i)
        weight[i][i] = 0;
}

pii make_edge(int u, int v)
{
    return mp(min(u, v), max(u, v));
}

void init_single_source(int s)
{
    for (auto& v: active_vertices)
        g[v][s]=inf, next_hop[v][s]=-1;
    g[s][s]=0;
}

void relax(int s, int u, int v)
{
    if (g[v][s] > g[u][s] + weight[u][v])
        g[v][s] = g[u][s] + weight[u][v],
        next_hop[v][s] = u;
}

/*class my_comp {
    int s;
    public:
        my_comp(int x) : s(x) {}
        bool foo(int a, int b) {return g[a][s] < g[b][s];}
};*/

void dijkstra_(int s)
{
    init_single_source(s);
    auto my_comp = [s](int v, int u)->bool{return g[v][s]<g[u][s];};
    
    multiset<int, decltype(my_comp)> q(my_comp);
    map<int, decltype(q.begin())> M;
    for (auto v: active_vertices)
        M[v]=q.insert(v);
    while (not q.empty()) {
        auto it = q.begin();
        int u = *it;
        q.erase(it);
        M[u] = q.end();
        for (auto v: adj[u]) {
            if (M[v] == q.end()) continue;
            q.erase(M[v]);
            relax(s, u, v);
            M[v]=q.insert(v);
        }
    }
}

void shortest_path()
{
    for (auto& i: active_vertices)
        dijkstra_(i);
}

void remove_long_edge(ll cmax)
{
    for (int i=1; i<=n; ++i)
        for (auto it = adj[i].begin(); it != adj[i].end(); )
            if (g[i][*it] < weight[i][*it] or weight[i][*it] > cmax) {
#ifdef DEBUG
                cout<<"Removing "<<i<<"-"<<*it<<endl;
#endif
                adj[*it].erase(i),it = adj[i].erase(it); 
            }
            else ++it;
}

void remove_leaf_non_terminals(int j)
{
    while(not removed[j] and not is_terminal[j] and adj[j].size()==1) {
        auto p = *adj[j].begin();
        adj[p].erase(j);
        adj[j].clear( );
        removed[j]=1;
        active_vertices.erase(j);
#ifdef DEBUG
        cout<<"Removing "<<j<<endl;
#endif
        j=p;
    }
}

void contract(int u, int v)
{
    for (auto& k : adj[v]) 
        if (k!=u) {
            if (weight[u][k] > weight[v][k])
                edge_map[make_edge(u,k)].pb(make_edge(v,k));
            adj[u].insert(k),
            adj[k].insert(u),
            adj[k].erase (v),
            weight[u][k]   =
            weight[k][u]   =
            min(weight[u][k],
                weight[v][k]);    
        }
    steiner.pb(make_edge(u,v));
    adj[u].erase(v);
    adj[v].clear( );
    is_terminal[u] |= is_terminal[v];
    removed[v]=1;
    active_vertices.erase(v);
}

void remove_non_terminals()
{
    for (int i=1; i<=n; ++i) 
        remove_leaf_non_terminals(i);
    
    for (int i=1; i<=n; ++i) {
        if (removed[i] or is_terminal[i] or adj[i].size()>2) continue;
        queue<int> q;
        q.push(i);
        set<int> vis;
        vis.insert(i);
        while (not q.empty()) {
            int x = q.front();
            q.pop();
            if (removed[x] or adj[x].size()==1) continue;
            int u = *adj[x].begin();
            int v = *next(adj[x].begin());
            removed[x]=1;
            active_vertices.erase(x);
#ifdef DEBUG
            cout<<"Removing (mid term): "<<x<<endl;
#endif
            adj[u].erase(x), adj[v].erase(x);
            adj[x].clear();
            if (weight[u][x] + weight[x][v] < weight[u][v])
                edge_map[make_edge(u,v)].pb(make_edge(u,x)),
                edge_map[make_edge(u,v)].pb(make_edge(x,v));
            adj[u].insert(v), adj[v].insert(u);
            weight[u][v] = weight[v][u] = min(weight[u][v], weight[u][x] + weight[x][v]);
            remove_leaf_non_terminals(u), remove_leaf_non_terminals(v);
            if (not is_terminal[u] and adj[u].size() == 2 and not vis.count(u)) 
                q.push(u), vis.insert(u);
            if (not is_terminal[v] and adj[v].size() == 2 and not vis.count(v)) 
                q.push(v), vis.insert(v);
        }
    }
}

void preprocess()
{
    //cout<<"removed long edges.."<<endl;
    remove_non_terminals();
    for (int i=1; i<=n; ++i)
        if (not removed[i] and is_terminal[i])
            while (adj[i].size() == 1) contract(i, *adj[i].begin());
    
    for (int i=1; i<=n; ++i)
        if (not removed[i] and is_terminal[i]) {
            while(adj[i].size()==2)  {
                auto j = *adj[i].begin(), k = *next(adj[i].begin());
                if (is_terminal[j] and weight[i][j]<=weight[i][k])
                    contract(i, j);
                else if (is_terminal[k] and weight[i][k]<=weight[i][j])
                    contract(i, k);
                else break;
            }
        }
    
    for (int i=1; i<=n; ++i) {
        if (removed[i] or not is_terminal[i]) continue;
        while (1) {
            ll miw=inf; int k=0;
            for (auto& j: adj[i]) 
                if (weight[i][j] < miw or weight[i][j] == miw and is_terminal[j]) 
                    miw=weight[i][j], k=j;
            if (is_terminal[k]) contract(i, k);
            else break;
        }
    }
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
    while (i != j) steiner.pb(make_edge(i, next_hop[i][j])), i=next_hop[i][j];
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
    int k = term.size();
    if (k<=1) return;
    if (k==2) {
        print_actual_path(term[0],term[1]);
        return;
    }
    map<pair<string, int>, ll> dp;
    map<pair<string, int>, pair<int, pair<string, string>>> tree;
    int q = term.back();
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
    print_path(C,q,tree);
}

template<class T>
void print_set(set<T>& s)
{
    for (auto& i: s)
        cout<<i<<" ";
    cout<<endl;
}

void unroll(pii e, set<pii>& reals, ll& ans)
{
    if (edge_map.find(e) == edge_map.end()) {
        ans += weight[e.ff][e.ss], reals.insert(e);
        return;
    }
    for (auto &i : edge_map[e])
        unroll(i, reals, ans);
}

ll maxSD()
{
    auto my_comp = [](pii a, pii b)->bool{return g[a.ff][a.ss] < g[b.ff][b.ss];};
    multiset<pii, decltype(my_comp)> edges(my_comp);
    int n_terminals = 0;
    for (auto& i: active_vertices) {
        if (not is_terminal[i]) continue;
        ++n_terminals;
        for (auto &j : active_vertices) {
            if (j==i or not is_terminal[j]) continue;
            edges.insert(make_edge(i, j));
        }
    }

    dsu D(n+1);
    ll cmax=-1;

    int m = n_terminals-1;
    while (m) {
        auto p = edges.begin();
        if (D.find_set(p->ff) != D.find_set(p->ss))
            cmax = g[p->ff][p->ss], D.union_(p->ff, p->ss), --m;
        edges.erase(p);
    }

    if (cmax==-1) return inf;
    return cmax;
}

int main(int argc, char** argv)
{
    ios::sync_with_stdio(false);
    input(cin);
//    shortest_path();
    preprocess();
    shortest_path();
    ll c_max = maxSD();
    remove_long_edge(c_max);
    vi term;
    for (int i=1; i<=n; ++i) 
        if (not removed[i] and is_terminal[i]) term.pb(i);
    

    int num_bccs = label_bccs(term[0]);
    add_terminals(term[0]);
#ifdef DEBUG
    cout<<"Number of bccs: "<<num_bccs<<endl;
#endif
    for (auto& vert: components) {
#ifdef DEBUG
        print_set(vert);
#endif
        solve(vert);
    }

    ll ans=0;
    set<pii> real_edges;
    for (auto& e: steiner)
        unroll(e, real_edges, ans);
    cout<<"VALUE "<<ans<<"\n";
    for (auto& e: real_edges)
        cout<<e.ff<<" "<<e.ss<<"\n";
	return 0;
}
