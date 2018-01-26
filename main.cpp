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

int n, m, k;
vector<vll> g;
vvi next_hop;
vi term;
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
        if (s=="Nodes") ss>>n, g.resize(n+1, vll(n+1, inf)), next_hop.resize(n+1, vi(n+1));
        if (s=="Edges") ss>>m;
        if (s=="E") {
            int u, v;ll w;ss>>u>>v>>w;
            g[u][v] = g[v][u] = min(g[u][v], w);
            next_hop[u][v] = v, next_hop[v][u] = u;
        }
        if (s=="Terminals") ss>>k;
        if (s=="T") {
            int t;ss>>t;
            term.pb(t);
        }
        if (s=="EOF") break;
    }
    for (int i=0; i<=n; ++i)
        g[i][i] = 0, next_hop[i][i] = i;
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

void print_path(string s, int q)
{
    if (s==string(k-1,'0')) return;
    int p = tree[mp(s,q)].ff;
    print_actual_path(q, p);
    string e = tree[mp(s,q)].ss.ff, f = tree[mp(s,q)].ss.ss;
    print_path(e, p);
    print_path(f, p);
}

void solve()
{
    int q = term.back();
    term.pop_back();
    for (int i=0; i<term.size(); ++i) {
        string t(k-1, '0');
        t[i]='1';
        for (int j=1; j<=n; ++j)
            dp[mp(t,j)] = g[term[i]][j],
            tree[mp(t, j)] = mp(term[i], mp(string(k-1,'0'), string(k-1, '0')));
    }
    for (int m=2; m<term.size(); ++m) {
        string D(k-1, '0'); 
        for (int i=k-1-m; i<k-1; ++i)
            D[i]='1';
        do {
            for (int i=1; i<=n; ++i)
                dp[mp(D,i)]=inf;
            for (int j=1; j<=n; ++j) {
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
                for (int i=1; i<=n; ++i)
                    if (dp[mp(D,i)] > g[i][j] + u)
                        dp[mp(D,i)] = g[i][j] + u,
                        tree[mp(D,i)] = mp(j, mp(e,f));
            }
        }while (next_permutation(D.begin(), D.end()));
    }
    string C(k-1, '1');
    for (int j=1; j<=n; ++j) {
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
    
    else if (k==2) 
        cout<<"VALUE "<<g[term[0]][term[1]]<<"\n",
        print_actual_path(term[0], term[1]);
    
    else solve();
	return 0;
}
