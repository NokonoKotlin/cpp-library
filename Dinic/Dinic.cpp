#include<vector>
#include<cassert>
#include<queue>
#include<unordered_map>
using std::vector;
using std::queue;
using std::pair;
using std::unordered_map;
/*   
    Copyright ©️ (c) NokonoKotlin (okoteiyu) 2024.
    Released under the MIT license(https://opensource.org/licenses/mit-license.php) 
*/
template<typename T = long long>
class mxfl{
    private :
    struct edge{
        int u,v;
        T cap;
        edge* r_edge;
        edge(int u_ , int v_ , T cap_):u(u_),v(v_),cap(cap_){}
    };
    int V;
    const int UNDEFINED_NODE = -1;
    const int UNREACHED = -1;
    const T ZERO_EPS = 0;
    vector<unordered_map<int,edge*>> E;
    vector<vector<pair<int,const edge*>>> G;
    vector<unordered_map<int,T>> F;
    vector<int> iter;
    vector<int> backward;
    vector<int> dist;
    public:
    mxfl(int V_)
    :V(V_),E(V_),G(V_),F(V_)
    ,dist(V_,UNREACHED),iter(V_,0),backward(V_,UNDEFINED_NODE){}
    ~mxfl(){
        for(int i = 0 ; i < V ; i++){
            for(pair<int,edge*> e: E[i]){
                if(i < e.first)delete e.second;
            }
        }
    }
    void add_edge(int u , int v , T c){
        assert(u != v);
        if(E[u][v] != nullptr && E[v][u] != nullptr){
            E[u][v]->cap += c;
            return;
        }
        assert(E[u][v] == nullptr && E[v][u] == nullptr);
        E[u][v] = new edge(u,v,c);
        E[v][u] = new edge(v,u,0);
        E[u][v]->r_edge = E[v][u];
        E[v][u]->r_edge = E[u][v];
        G[u].push_back({v,E[u][v]});
        G[v].push_back({u,E[v][u]});
    }
    void bfs(int s){
        vector<int>(V,UNREACHED).swap(dist);
        vector<int>(V,0).swap(iter);
        queue<int> q;q.push(s);
        dist[s] = 0;
        while(!q.empty()){
            int now = q.front();
            q.pop();
            for(pair<int,const edge*> e : G[now]){
                if(e.second == nullptr)continue;
                if(dist[e.first] != UNREACHED)continue;
                if(e.second->cap <= ZERO_EPS )continue;
                dist[e.first] = dist[now]+1;
                q.push(e.first);
            }
        }
    }
    vector<edge*> path(int s , int t){
        assert(s!=t);
        vector<edge*> res(0);
        int now = s;
        while(now != UNDEFINED_NODE){
            if(now == t)break;
            for(;iter[now] < G[now].size(); iter[now]++ ){
                pair<int,const edge*> e = G[now][iter[now]];
                if(e.second == nullptr)continue;
                if(e.second->cap <= ZERO_EPS)continue;
                if(dist[e.first] <= dist[now])continue;
                break;
            }
            if(G[now].size() <= iter[now]){
                now = backward[now];
                if(res.size() != 0)res.pop_back();
                if(now != UNDEFINED_NODE)iter[now]++;
            }else{
                pair<int,const edge*> e = G[now][iter[now]];
                backward[e.first] = now;
                res.push_back(const_cast<edge*>(e.second));
                now = e.first;
            }
        }
        return res;
    }
    bool Flow(int s , int t , T f){
        bfs(s);
        if(dist[t] == UNREACHED)false;
        vector<edge*> p = path(s,t);
        if(p.size()==0)return false;
        T bottle_neck = p.back()->cap;
        for(const edge* e : p)bottle_neck = min(bottle_neck,e->cap);
        if(bottle_neck < f)return false;
        for(edge* e : p){
            F[e->u][e->v] += f;
            e->cap -= f;
            e->r_edge->cap += f;
            F[e->v][e->u] -= f;
        }
        return true;
    }
    T MaxFlow(int s , int t){
        T res = 0;
        vector<edge*> p;
        while(true){
            bfs(s);
            if(dist[t] == UNREACHED)break;
            while((p = path(s,t)).size() != 0){
                T bottle_neck = p.back()->cap;
                for(const edge* e : p)bottle_neck = min(bottle_neck,e->cap);
                res += bottle_neck;
                for(edge* e : p){
                    F[e->u][e->v] += bottle_neck;
                    e->cap -= bottle_neck;
                    e->r_edge->cap += bottle_neck;
                    F[e->v][e->u] -= bottle_neck;
                }
            }
        }
        return res;
    }
    vector<edge> edges(){
        vector<edge> res;
        for(int x = 0 ; x < V ; x++)for(pair<int,T> e : F[x])res.emplace_back(x,e.first,e.second);
        return res;
    }
    /*   
        Copyright ©️ (c) NokonoKotlin (okoteiyu) 2024.
        Released under the MIT license(https://opensource.org/licenses/mit-license.php) 
    */
};
