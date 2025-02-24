#include<vector>
#include<unordered_map>
#include<cassert>
#include<string>
#include<cmath>
#include<algorithm>
#include<iostream>
#include<deque>
#include<stack>
#include<sstream>
#include<numeric>
#include<functional>

using std::pair;
using std::deque;
using std::stack;
using std::function;
using std::cout;
using std::ostringstream;
using std::numeric_limits;
using std::endl;
using std::cerr;
using std::min;
using std::max;
using std::swap;
using std::reverse;
using std::string;
using std::vector;
using std::unordered_map;

template<typename index_int , typename T>
struct PersistentDynamicSegmentTree{
    /*   
        Copyright ©️ (c) NokonoKotlin (okoteiyu) 2025.
        Released under the MIT license(https://opensource.org/licenses/mit-license.php) 
    */
    inline static const long long FIRST_VERSION = 0;
    inline static const long long ONETIME_VERSION = -1;
    struct Node{
        Node* left = nullptr;
        Node* right = nullptr;
        enum ChildValidation{INVALID , NOCHILD , BOTH};
        inline constexpr ChildValidation valid_check_child(){
            if(this->left == nullptr && this->right == nullptr)return NOCHILD;
            if(this->left != nullptr && this->right != nullptr)return BOTH;
            return INVALID;
        }
        int node_version;
        const index_int rangeLeft , rangeRight;
        inline constexpr index_int range_length()const{return (this->rangeRight - this->rangeLeft);}
        inline constexpr index_int range_mid()const{return ((this->rangeLeft+this->rangeRight)>>1);}
        T Sum, Max, Min;
        T ProdSum;
        inline static const pair<T,T> eq_affine = {T(1),T(0)};
        pair<T,T> lazy_affine = eq_affine;
        inline void set_lazyAffine(T a, T b){
            this->lazy_affine = {a*this->lazy_affine.first , a*this->lazy_affine.second + b};
        }
        private:
        Node(const Node& p) = default;
        public:
        Node(Node&& p) = default;
        Node(){}
        Node(const Node& nd , int ver) : Node(nd) {
            node_version = ver;
        }
        Node(index_int l , index_int r , T x , int ver) : rangeLeft(l) , rangeRight(r) , node_version(ver){
            Max = x;
            Min = x;
            Sum = range_length()*x;
            ProdSum = (x*((rangeRight-1)*rangeRight-(rangeLeft-1)*rangeLeft))/T(2);
        }
        void NodeUpdate(){
            ChildValidation c_state = this->valid_check_child();
            assert(c_state != INVALID);
            if(range_length() == 1){
                Sum = Min = Max;
                ProdSum = Max*rangeLeft;
                return;
            }
            assert(c_state != NOCHILD);
            this->eval(false,false);
            this->left->eval(false,false);
            this->right->eval(false,false);
            this->Sum = this->left->Sum + this->right->Sum;
            this->Min = min(this->left->Min, this->right->Min);
            this->Max = max(this->left->Max, this->right->Max);
            this->ProdSum = this->left->ProdSum + this->right->ProdSum;
        }
        void eval(bool make_child , bool inplace_forced){
            if(!make_child)assert(!inplace_forced);
            ChildValidation c_state = this->valid_check_child();
            assert(c_state != INVALID);
            if(this->lazy_affine != eq_affine){
                this->Min = this->lazy_affine.first * this->Min + this->lazy_affine.second;
                this->Max = this->lazy_affine.first * this->Max + this->lazy_affine.second;
                this->Sum = this->lazy_affine.first * this->Sum + this->lazy_affine.second * this->range_length();
                this->ProdSum = this->lazy_affine.first * this->ProdSum + ((this->lazy_affine.second*((rangeRight-1)*rangeRight - (rangeLeft-1)*rangeLeft))/T(2));
                if(this->Max < this->Min)swap(this->Max,this->Min);
                if(this->valid_check_child() == BOTH){
                    assert(this->node_version != this->left->node_version && this->node_version != this->right->node_version);
                    this->left = new Node(*(this->left),this->node_version);
                    this->right = new Node(*(this->right),this->node_version);
                    this->left->set_lazyAffine(this->lazy_affine.first,this->lazy_affine.second);
                    this->right->set_lazyAffine(this->lazy_affine.first,this->lazy_affine.second);
                }
                this->lazy_affine = eq_affine;
            }
            if(this->range_length() <= 1 || make_child == false)return;
            if(c_state == BOTH && inplace_forced == false)return;
            if(c_state == BOTH && inplace_forced){
                if(this->node_version != this->left->node_version)this->left = new Node(*(this->left),this->node_version);
                if(this->node_version != this->right->node_version)this->right = new Node(*(this->right),this->node_version);
                return;
            }
            assert(c_state == NOCHILD);
            this->left = new Node(this->rangeLeft,this->range_mid(),this->Max , this->node_version);
            this->right = new Node(this->range_mid(),this->rangeRight,this->Max , this->node_version);
        }
    };
    inline static bool cover(index_int l , index_int r , index_int i){
        return bool(l <= i && i < r);
    }
    inline static bool intersect(index_int l1 , index_int r1 , index_int l2 , index_int r2){
        return bool(l1 <= l2 && l2 < r1) || bool(l2 <= l1 && l1 < r2);
    }
    inline static index_int CommonArea(index_int l1 , index_int r1 , index_int l2 , index_int r2){
        if(!intersect(l1,r1,l2,r2))return 0;
        return min(r1,r2) - max(l1,l2);
    }
    private:
    index_int _Llim,_Rlim;
    const T init_value;
    vector<Node*> m_RootVersion;
    vector<vector<int>> update_flow = {{}};
    Node* m_OneTime_root = nullptr;
    void FreeOneTimeVersion(){
        if(m_OneTime_root == nullptr)return;
        stack<Node*> st;
        st.push(m_OneTime_root);
        while(!st.empty()){
            Node* now = st.top();
            st.pop();
            assert(now->node_version == ONETIME_VERSION);
            if(now->valid_check_child() == Node::BOTH){
                if(now->left->node_version == ONETIME_VERSION)st.push(now->left);
                if(now->right->node_version == ONETIME_VERSION)st.push(now->right);
            }
            delete now;
        }
        m_OneTime_root = nullptr;
    }
    vector<Node*> RangeDFSRoute(index_int l , index_int r , Node* rt){
        assert(rt->node_version == ONETIME_VERSION || rt->node_version > this->version());
        vector<Node*> res;
        stack<Node*> st;
        st.push(rt);
        while(!st.empty()){
            Node* now = st.top();
            assert(now->node_version == rt->node_version);
            assert(intersect(l , r , now->rangeLeft , now->rangeRight));
            st.pop();
            res.push_back(now);
            if(now->range_length() == 1 || CommonArea(l, r, now->rangeLeft , now->rangeRight) == now->range_length())continue;
            assert(now->range_length() >= 2);
            now->eval(true,bool(now->valid_check_child() == Node::NOCHILD));
            if(intersect(l,r,now->rangeLeft , now->range_mid())){
                if(now->left->node_version != rt->node_version)now->left = new Node(*(now->left) , rt->node_version);
                st.push(now->left);
            }
            if(intersect(l,r, now->range_mid() , now->rangeRight)){
                if(now->right->node_version != rt->node_version)now->right = new Node(*(now->right) , rt->node_version);
                st.push(now->right);
            }
        }
        return res;
    }
    vector<Node*> RangeOneTimeSegments(index_int l , index_int r){
        vector<Node*> dfs_route = RangeDFSRoute(l,r,m_OneTime_root);
        vector<Node*> res;
        for(Node* seg : dfs_route){
            assert(seg->node_version == ONETIME_VERSION);
            if(CommonArea(l,r,seg->rangeLeft,seg->rangeRight) != seg->range_length())continue;
            seg->eval(false,false);
            res.push_back(seg);
        }
        return res;
    }
    inline static void operate_update(T& a, T b){a = b;}
    inline static void operate_add(T& a , T b){a += b;}
    template<void (*upd)(T&,T)>
    void version_update(vector<pair<index_int,T>> queries , int ver){
        assert(ver != ONETIME_VERSION);
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(queries.size() > 0);
        sort(queries.begin(),queries.end(),[&](pair<index_int,T> a , pair<index_int,T> b){return bool(a.first < b.first);});
        Node* now = new Node(*m_RootVersion[ver] , m_RootVersion.size());
        m_RootVersion.push_back(now);
        deque<Node*> path;
        path.push_back(now);
        for(pair<index_int,T> q : queries){
            assert(Llimit() <= q.first && q.first < Rlimit());
            while(cover(now->rangeLeft,now->rangeRight,q.first) == false){
                path.back()->NodeUpdate();
                path.pop_back();
                now = path.back();
            }
            while(now->range_length() > 1){
                now->eval(true,false);
                assert(now->valid_check_child() == Node::BOTH);
                if(cover(now->left->rangeLeft , now->left->rangeRight , q.first)){
                    if(now->left->node_version != now->node_version)now->left = new Node(*(now->left),now->node_version);
                    path.push_back(now->left);
                }else{
                    if(now->right->node_version != now->node_version)now->right = new Node(*(now->right),now->node_version);
                    path.push_back(now->right);
                }
                now = path.back();
            }
            now->eval(true,false);
            assert(path.back()->range_length() == 1);
            upd(path.back()->Max,q.second);
        }
        while(path.size() > 0){
            path.back()->NodeUpdate();
            path.pop_back();
        }
        memo_versionflow(ver,this->version());
    }
    void memo_versionflow(int i , int j){
        while( update_flow.size() <= max(i,j))update_flow.emplace_back();
        update_flow[i].push_back(j);
    }
    public:
    PersistentDynamicSegmentTree()
        :_Llim(numeric_limits<index_int>::min()/2),_Rlim(numeric_limits<index_int>::max()/2)
            ,init_value(0),m_RootVersion(1,new Node(_Llim,_Rlim,init_value,0)){}
    PersistentDynamicSegmentTree(index_int L_ , index_int R_ , T init_value_)
        :_Llim(L_),_Rlim(R_),init_value(init_value_), m_RootVersion(1,new Node(L_,R_,init_value,0)){}
    ~PersistentDynamicSegmentTree(){}
    PersistentDynamicSegmentTree(const PersistentDynamicSegmentTree &x) = delete ;
    PersistentDynamicSegmentTree& operator = (const PersistentDynamicSegmentTree &x) = delete ;
    PersistentDynamicSegmentTree ( PersistentDynamicSegmentTree&& x){assert(0);}
    PersistentDynamicSegmentTree& operator = ( PersistentDynamicSegmentTree&& x){assert(0);}
    index_int Llimit(){return _Llim;}
    index_int Rlimit(){return _Rlim;}
    int version(){
        return int(m_RootVersion.size()) - 1;
    }
    void update_together(vector<pair<index_int,T>> queries , int ver){
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(queries.size() > 0);
        unordered_map<index_int,int> count;
        for(const pair<index_int,T>& p : queries){
            count[p.first]++;
            assert(count[p.first]<=1);
        }
        version_update<operate_update>(queries,ver);
    }
    void update(index_int i , T x , int ver){
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(Llimit() <= i && i < Rlimit());
        update_together({{i,x}},ver);
    }
    void add_together(vector<pair<index_int,T>> queries , int ver){
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(queries.size() > 0);
        version_update<operate_add>(queries,ver);
    }
    void add(index_int i , T x , int ver){
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(Llimit() <= i && i < Rlimit());
        add_together({{i,x}},ver);
    }
    void RangeCopy(index_int l , index_int r , int v1 , int v2){
        assert(FIRST_VERSION <= v1 && v1 <= this->version());
        assert(FIRST_VERSION <= v2 && v2 <= this->version());
        assert(Llimit() <= l && l < r && r <= Rlimit());
        Node* v1copy = new Node(*m_RootVersion[v1] , m_RootVersion.size());
        vector<Node*> RangeDFS_v1copy = RangeDFSRoute(l,r,v1copy);
        m_RootVersion.push_back(v1copy);
        m_OneTime_root = new Node(*m_RootVersion[v2] , ONETIME_VERSION);
        vector<Node*> RangeDFS_v2Resource = RangeDFSRoute(l,r,m_OneTime_root);
        for(int i = 0 ; i < RangeDFS_v1copy.size() ; i++){
            Node* new_v_node = RangeDFS_v1copy[i];
            Node* resource_node = RangeDFS_v2Resource[i];
            if(new_v_node->range_length() <= 1)continue;
            if(new_v_node->valid_check_child() == Node::NOCHILD)continue;
            resource_node->eval(true,false);
            assert(new_v_node->rangeLeft == resource_node->rangeLeft);
            assert(new_v_node->rangeRight == resource_node->rangeRight);
            assert(resource_node->valid_check_child() == Node::BOTH);
            if(!intersect(l,r,resource_node->left->rangeLeft,resource_node->left->rangeRight)){
                if(new_v_node->left->node_version == new_v_node->node_version){
                    if(new_v_node->left->valid_check_child() == Node::BOTH){
                        assert(new_v_node->left->left->node_version != ONETIME_VERSION);
                        assert(new_v_node->left->right->node_version != ONETIME_VERSION);
                    }
                    delete new_v_node->left;
                }
                new_v_node->left = resource_node->left;
                if(new_v_node->left->node_version == ONETIME_VERSION){
                    if(new_v_node->left->valid_check_child() == Node::BOTH){
                        assert(new_v_node->left->left->node_version != ONETIME_VERSION);
                        assert(new_v_node->left->right->node_version != ONETIME_VERSION);
                    }
                    new_v_node->left->node_version = new_v_node->node_version;
                }
            }
            if(!intersect(l,r,resource_node->right->rangeLeft,resource_node->right->rangeRight)){
                if(new_v_node->right->node_version == new_v_node->node_version){
                    if(new_v_node->right->valid_check_child() == Node::BOTH){
                        assert(new_v_node->right->left->node_version != ONETIME_VERSION);
                        assert(new_v_node->right->right->node_version != ONETIME_VERSION);
                    }
                    delete new_v_node->right;
                }
                new_v_node->right = resource_node->right;
                if(new_v_node->right->node_version == ONETIME_VERSION){
                    if(new_v_node->right->valid_check_child() == Node::BOTH){
                        assert(new_v_node->right->left->node_version != ONETIME_VERSION);
                        assert(new_v_node->right->right->node_version != ONETIME_VERSION);
                    }
                    new_v_node->right->node_version = new_v_node->node_version;
                }
            }
        }
        reverse(RangeDFS_v1copy.begin(),RangeDFS_v1copy.end());
        for(Node* nd : RangeDFS_v1copy){
            assert(nd->node_version == this->version());
            if(nd->valid_check_child() == Node::NOCHILD)continue;
            nd->NodeUpdate();
        }
        this->FreeOneTimeVersion();
        memo_versionflow(v1,this->version());
        memo_versionflow(v2,this->version());
    }
    Node RangeMerge(index_int l , index_int r , int ver){
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(Llimit() <= l && l < r && r <= Rlimit());
        m_OneTime_root = new Node(*m_RootVersion[ver],ONETIME_VERSION);
        vector<Node*> bucket = RangeOneTimeSegments(l,r);
        assert(bucket.size() > 0);
        Node ProductNode(*bucket[0],ONETIME_VERSION);
        ProductNode.left = nullptr;
        ProductNode.right = nullptr;
        for(int i = 1 ; i < bucket.size() ; i++){
            ProductNode.Max = max(ProductNode.Max, bucket[i]->Max);
            ProductNode.Min = min(ProductNode.Min, bucket[i]->Min);
            ProductNode.Sum = ProductNode.Sum + bucket[i]->Sum;
            ProductNode.ProdSum = ProductNode.ProdSum + bucket[i]->ProdSum;
        }
        this->FreeOneTimeVersion();
        return ProductNode;
    }
    void RangeAffine(index_int l , index_int r, T A , T B, int ver){
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(Llimit() <= l && l < r && r <= Rlimit());
        Node* nRoot = new Node(*m_RootVersion[ver] , m_RootVersion.size());
        vector<Node*> DfsRoute = RangeDFSRoute(l,r,nRoot);
        m_RootVersion.push_back(nRoot);
        reverse(DfsRoute.begin(),DfsRoute.end());
        for(Node* nd : DfsRoute){
            assert(nd->node_version == nRoot->node_version);
            if(CommonArea(l,r,nd->rangeLeft , nd->rangeRight) == nd->range_length())nd->set_lazyAffine(A,B);
            else nd->NodeUpdate();
        }
        this->FreeOneTimeVersion();
        memo_versionflow(ver,this->version());
    }
    void RangeAdd(index_int l , index_int r, T x, int ver){
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(Llimit() <= l && l < r && r <= Rlimit());
        RangeAffine(l,r,T(1),x,ver);
    }
    void RangeUpdate(index_int l , index_int r, T x , int ver){
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(Llimit() <= l && l < r && r <= Rlimit());
        RangeAffine(l,r,T(0),x,ver);
    }
    T get(index_int i , int ver){
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(Llimit() <= i && i < Rlimit());
        return RangeMerge(i,i+1,ver).Max;
    }
    template<typename type_merge>
    index_int binsearch_on_segtree(
            const index_int L , const index_int R ,
            type_merge Eq , function<T(type_merge , Node*)> op ,
            function<bool(type_merge)> judge , int ver){
        assert(FIRST_VERSION <= ver && ver <= this->version());
        m_OneTime_root = new Node(*m_RootVersion[ver],ONETIME_VERSION);
        vector<Node*> bucket = RangeOneTimeSegments(L,R);
        vector<type_merge> prefixprod;
        type_merge prod = Eq;
        for(Node* tmp : bucket){
            prod = op(prod,tmp);
            prefixprod.push_back(prod);
        }
        while(bucket.size() != 0){
            prod = Eq;
            Node* tmp = bucket.back();
            assert(tmp->node_version == ONETIME_VERSION);
            tmp->eval(true,true);
            if(tmp->valid_check_child() == Node::BOTH){
                assert(tmp->left->node_version == ONETIME_VERSION);
                assert(tmp->right->node_version == ONETIME_VERSION);
            }
            prefixprod.pop_back();
            bucket.pop_back();
            if(prefixprod.size()>0)prod = prefixprod.back();
            if(judge(prod))continue;
            bucket.push_back(tmp);
            prod = op(prod,tmp);
            prefixprod.push_back(prod);
            if(bucket.back()->range_length() <= 1)break;
            prod = Eq;
            bucket.pop_back();
            prefixprod.pop_back();
            if(prefixprod.size()>0)prod = prefixprod.back();
            bucket.push_back(tmp->left);
            tmp->left->eval(false,false);
            prefixprod.push_back(op(prod,tmp->left));
            bucket.push_back(tmp->right);
            tmp->right->eval(false,false);
            prefixprod.push_back(op(op(prod,tmp->left),tmp->right));
        }
        assert(bucket.size() > 0);
        index_int res = bucket.back()->rangeRight;
        this->FreeOneTimeVersion();
        return res;
    }
    template<typename F>string format_num(F x , int digit_size = 4){
        ostringstream sout;
        sout.precision(digit_size+1);
        sout<<x;
        string res = sout.str();
        if(res.size() > digit_size){
            while(res.size() > digit_size)res.pop_back();
            res.back() = '~';
        }
        while(res.size() < digit_size)res.push_back(' ');
        return res;
    }
    template<int digit_size = 4>
    void DebugFlow(int l , int r){
        vector<pair<int,int>> update_info;
        for(int i = 0 ; i <= this->version();i++){
            for(int j : update_flow[i])update_info.emplace_back(i,j);
        }
        vector<vector<int>> debug_symbol(this->version()+1, vector<int>(update_info.size(),0));
        sort(update_info.begin(),update_info.end(),[&](pair<int,int> a , pair<int,int> b){
            if(update_flow[a.first].size() == update_flow[b.first].size()){
                if(a.first == b.first)return bool(a.second > b.second);
                return bool(a.first > b.first);
            }
            return bool(update_flow[a.first].size() < update_flow[b.first].size());
        });
        for(int flow_num = 0; flow_num < update_info.size() ; flow_num++){
            int ref = update_info[flow_num].first;
            int call = update_info[flow_num].second;
            for(int i = ref + 1 ; i < call ; i++)debug_symbol[i][flow_num] = 3;
            debug_symbol[ref][flow_num] = 1;
            debug_symbol[call][flow_num] = 2;
        }
        for(int i = 1 ; i < update_info.size() ; i++)cerr << "  ";
        cerr << "| update flow in range [" << l << " , " << r << ")" << endl;
        for(int i = 1 ; i < update_info.size() ; i++)cerr << "  ";
        cerr << "index  | ";
        for(int j = l ; j < r ; j++)cerr << format_num<T>(j,digit_size-1) << "| ";
        cerr << endl;
        for(int i = 0 ; i < debug_symbol.size() ; i++){
            for(int j = 0 ; j < debug_symbol[i].size() ; j++){
                if(debug_symbol[i][j] == 1)cerr << "F ";
                else if(debug_symbol[i][j] == 2)cerr << "L ";
                else if(debug_symbol[i][j] == 3)cerr << "| ";
                else cerr << "  ";
            }
            cerr << "ver " << format_num<int>(i,3) << ": ";
            for(int j = l ; j < r ; j++)cerr << format_num<T>(this->get(j,i),digit_size) << " ";
            cerr << endl;
        }
    }
    /*   
        Copyright ©️ (c) NokonoKotlin (okoteiyu) 2025.
        Released under the MIT license(https://opensource.org/licenses/mit-license.php) 
    */
};

template<typename type_key , typename type_size>
struct PersistentSegTreeSet{
    /*   
        Copyright ©️ (c) NokonoKotlin (okoteiyu) 2025.
        Released under the MIT license(https://opensource.org/licenses/mit-license.php) 
    */
    using Node = PersistentDynamicSegmentTree<type_key , type_size>::Node;
    inline static const int FIRST_VERSION = PersistentDynamicSegmentTree<type_key , type_size>::FIRST_VERSION;
    private:
    PersistentDynamicSegmentTree<type_key, type_size> S;
    type_size m_size = 0;
    type_key key_min,key_max;
    public:
    PersistentSegTreeSet(type_key key_min_ = -1000000001 ,type_key key_max_ = 1000000001)
        :key_min(key_min_), key_max(key_max_), S(key_min_,key_max_+1,0){}
    PersistentSegTreeSet(const PersistentSegTreeSet &x) = delete ;
    PersistentSegTreeSet& operator = (const PersistentSegTreeSet &x) = delete ;
    PersistentSegTreeSet ( PersistentSegTreeSet&& x){assert(0);}
    PersistentSegTreeSet& operator = ( PersistentSegTreeSet&& x){assert(0);}
    type_key max_limit(){return key_max;}
    type_key min_limit(){return key_min;}
    int version(){
        return this->S.version();
    }
    type_size size( int ver){
        assert(FIRST_VERSION <= ver && ver <= this->version());
        return S.RangeMerge(S.Llimit(),S.Rlimit(),ver).Sum;
    }
    void insert_together(vector<pair<type_key,type_size>> queries , int ver){
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(queries.size() > 0);
        for(int i = 0 ; i < queries.size() ; i++){
            assert(min_limit() <= queries[i].first && queries[i].first <= max_limit());
            assert(queries[i].second >= 0);
        }
        S.add_together(queries,ver);
    }
    void insert(type_key x , type_size c , int ver){
        assert(min_limit() <= x && x <= max_limit());
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(c>=0);
        S.add(x,c,ver);
    }
    void erase_together(vector<pair<type_key,type_size>> queries , int ver){
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(queries.size() > 0);
        for(int i = 0 ; i < queries.size() ; i++){
            assert(min_limit() <= queries[i].first && queries[i].first <= max_limit());
            assert(queries[i].second >= 0);
            queries[i].second *= -1;
        }
        S.add_together(queries,ver);
        for(int i = 0 ; i < queries.size() ; i++)assert(this->S.get(queries[i].first) >= 0);
    }
    void erase(type_key x , type_size c, int ver){
        assert(min_limit() <= x && x <= max_limit());
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(c>=0);
        assert(S.get(x,ver) >= c);
        S.add(x,-c,ver);
    }
    void set_together(vector<pair<type_key,type_size>> queries , int ver){
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(queries.size() > 0);
        for(int i = 0 ; i < queries.size() ; i++){
            assert(min_limit() <= queries[i].first && queries[i].first <= max_limit());
            assert(queries[i].second >= 0);
        }
        S.update_together(queries,ver);
    }
    type_size lower_bound(type_key x, int ver){
        assert(min_limit() <= x && x <= max_limit()+1);
        assert(FIRST_VERSION <= ver && ver <= this->version());
        if(x == key_min)return type_size(0);
        return S.RangeMerge(key_min,x,ver).Sum;
    }
    type_size upper_bound(type_key x, int ver){
        assert(min_limit() <= x && x <= max_limit());
        assert(FIRST_VERSION <= ver && ver <= this->version());
        return S.RangeMerge(key_min,x+1,ver).Sum;
    }
    type_size count(type_key x, int ver){
        assert(min_limit() <= x && x <= max_limit());
        assert(FIRST_VERSION <= ver && ver <= this->version());
        return S.get(x, ver);
    }
    type_size count(type_key k_l , type_key k_r, int ver){
        assert(min_limit() <= k_l && k_l < k_r && k_r <= max_limit()+1);
        assert(FIRST_VERSION <= ver && ver <= this->version());
        return S.RangeMerge(k_l,k_r,ver).Sum;
    }
    type_size find(type_key x , int ver){
        assert(min_limit() <= x && x <= max_limit());
        if(this->count(x,ver) == 0)return -1;
        return this->lower_bound(x,ver);
    }
    type_size get_sum(type_key k_l , type_key k_r , int ver){
        assert(min_limit() <= k_l && k_l < k_r && k_r <= max_limit()+1);
        assert(FIRST_VERSION <= ver && ver <= this->version());
        return S.RangeMerge(k_l,k_r,ver).ProdSum;
    }
    type_size range_sum(type_size l ,type_size r, int ver){
        assert(0 <= l && l < r && r <= size(ver));
        assert(FIRST_VERSION <= ver && ver <= this->version());
        type_size res = 0;
        type_key Lkey = this->get(l,ver);
        res += Lkey*(this->count(min_limit() , Lkey+1,ver) - l);
        if(this->size(ver)<=r){
            if(Lkey+1 <= key_max)res += this->get_sum(Lkey+1,key_max+1,ver);
            return res;
        }
        type_key Rkey = this->get(r ,ver);
        if(Lkey == Rkey)return (r-l)*Lkey;
        res += Rkey*(r - this->count(min_limit() , Rkey , ver));
        if(Lkey+1 < Rkey)res += this->get_sum(Lkey+1,Rkey,ver);
        return res;
    }
    void range_insert(type_key k_l , type_key k_r , type_size c, int ver){
        assert(min_limit() <= k_l && k_l < k_r && k_r <= max_limit()+1);
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(c>=0);
        S.RangeAdd(k_l,k_r,c,ver);
    }
    void range_erase(type_key k_l , type_key k_r , type_size c, int ver){
        assert(min_limit() <= k_l && k_l < k_r && k_r <= max_limit()+1);
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(S.RangeMerge(k_l,k_r,ver).Min >= c);
        S.RangeAdd(k_l,k_r,c*type_size(-1),ver);
    }
    void multiple_insert(type_key k_l , type_key k_r , type_size c, int ver){
        assert(min_limit() <= k_l && k_l < k_r && k_r <= max_limit()+1);
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(c>=1);
        S.RangeAffine(k_l,k_r,c,type_size(0),ver);
    }
    void uniform_insert(type_key k_l , type_key k_r , type_size c, int ver){
        assert(min_limit() <= k_l && k_l < k_r && k_r <= max_limit()+1);
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(c>=0);
        S.RangeUpdate(k_l,k_r,c,ver);
    }
    type_key get(type_size ind , int ver){
        assert(0 <= ind && ind < size(ver));
        assert(FIRST_VERSION <= ver && ver <= this->version());
        type_size Eq = 0;
        function<type_size(type_size,Node*)> op = [&](type_size p , Node* nd){return p+nd->Sum;};
        type_size border_value = ind+1;
        function<bool(type_size)> judge = [&](type_size val){return bool(val >= border_value);};
        type_key border_ok = S.binsearch_on_segtree(min_limit(),max_limit()+1,Eq,op,judge,ver);
        assert(min_limit() < border_ok);
        assert(judge(S.RangeMerge(min_limit(),border_ok,ver).Sum));
        return border_ok - 1;
    }
    type_key minimum_freq(type_key L, type_key R , int ver){
        assert(min_limit() <= L && L < R && R <= max_limit()+1);
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(this->count(L,R,ver) > 0);
        type_size Eq = S.RangeMerge(L,R,ver).Max+1;
        function<type_size(type_size,Node*)> op = [&](type_size p , Node* nd){return min(p,nd->Min);};
        type_size border_value = S.RangeMerge(L,R,ver).Min;
        function<bool(type_size)> judge = [&](type_size val){return bool(val <= border_value);};
        type_key border_ok = S.binsearch_on_segtree(L,R,Eq,op,judge,ver);
        assert(L < border_ok);
        assert(judge(S.RangeMerge(L,border_ok,ver).Min));
        return border_ok - 1;
    }
    type_key maximum_freq(type_key L, type_key R, int ver){
        assert(min_limit() <= L && L < R && R <= max_limit()+1);
        assert(FIRST_VERSION <= ver && ver <= this->version());
        assert(this->count(L,R,ver) > 0);
        type_size Eq = S.RangeMerge(L,R,ver).Min-1;
        function<type_size(type_size,Node*)> op = [&](type_size p , Node* nd){return max(p,nd->Max);};
        type_size border_value = S.RangeMerge(L,R,ver).Max;
        function<bool(type_size)> judge = [&](type_size val){return bool(val >= border_value);};
        type_key border_ok = S.binsearch_on_segtree(L,R,Eq,op,judge,ver);
        assert(L < border_ok);
        assert(judge(S.RangeMerge(L,border_ok,ver).Max));
        return border_ok - 1;
    }
    void Debug(int ver){
        assert(FIRST_VERSION <= ver && ver <= this->version());
        cerr << "version "<< ver << " : " << this->size(ver) << " element(s)."<< endl;
        unordered_map<type_key,int> viewed;
        for(type_size i = 0 ; i < this->size(ver) ; i++){
            if(viewed[this->get(i , ver)]++)continue;
            cerr << i << " th element = " << this->get(i , ver) << " x " << this->count(this->get(i,ver), ver) << endl;
        }
    }
    void DebugFlow(type_key l , type_key r){
        cerr << "| debug with counts of elements and " << endl;
        S.DebugFlow(l,r);
    }
    void test_rangecp(type_key l , type_key r , int v1 ,int v2 ){S.RangeCopy(l,r,v1,v2);}
    /*   
        Copyright ©️ (c) NokonoKotlin (okoteiyu) 2025.
        Released under the MIT license(https://opensource.org/licenses/mit-license.php) 
    */
};

void test_persistent_datastructure(){
    using ll = long long;
    using pll = pair<ll,ll>;
    using vpll = vector<pll>;
    using namespace std;
    ll Llim = -500;
    ll Rlim = 500;
    PersistentSegTreeSet<ll,ll> S(Llim , Rlim);
    PersistentSegTreeSet<ll,ll> LazyS(Llim , Rlim);
    int testcnt = 400000;
    vector<string> qtype(12,"undefined");
    qtype[0] = "insert_together(rand)";
    qtype[1] = "erase(x,c)";
    qtype[2] = "get(i)";
    qtype[3] = "count(x)";
    qtype[4] = "count(l,r)";
    qtype[5] = "get_sum(l,r)";
    qtype[6] = "range_sum(li,ri)";
    qtype[7] = "maximum_freq(l,r)";
    qtype[8] = "minimum_freq(l,r)";
    qtype[9] = "uniform_insert(l,r)";
    qtype[10] = "range_insert(l,r)";
    qtype[11] = "RangeCopy(l,r)";
    while(testcnt-->0){
        int t = rand()%12;
        ll x = Llim + rand()%(Rlim-Llim+1);
        int c = rand()%30+1;
        int v = rand()%(S.version()+1);
        ll l = Llim + rand()%(Rlim-Llim+1);
        ll r = Llim + rand()%(Rlim-Llim+1);
        if(l>r)swap(l,r);
        r++;
        ll li = rand()%S.size(v);
        ll ri = rand()%S.size(v);
        if(li>ri)swap(li,ri);
        ri++;
        if(t == 0){
            vector<pll> qrs;
            for(int i = 0 ; i < c ; i++)qrs.emplace_back(Llim + rand()%(Rlim-Llim+1),rand()%10+1);
            S.insert_together(qrs,v);
            LazyS.insert_together(qrs,v);
        }else if(t == 1){
            if(S.count(x,v) < c)c = S.count(x,v);
            S.erase(x,c,v);
            LazyS.erase(x,c,v);
        }else if(t == 2){
            if(S.size(v) > 0){
                int i = rand()%S.size(v);
                if(LazyS.get(i,v) != S.get(i,v)){
                    assert(LazyS.get(i,v) == S.get(i,v));
                }
            }
        }else if(t == 3){
            assert(LazyS.count(x,v) == S.count(x,v));
        }else if(t == 4){
            if(LazyS.count(l,r,v) != S.count(l,r,v)){
                assert(LazyS.count(l,r,v) == S.count(l,r,v));
            }
        }else if(t == 5){
            if(LazyS.get_sum(l,r,v) != S.get_sum(l,r,v)){
                assert(LazyS.get_sum(l,r,v) == S.get_sum(l,r,v));
            }
        }else if(t == 6){
            if(S.size(v) > 0 && 0){
                if(LazyS.range_sum(li,ri,v) != S.range_sum(li,ri,v)){
                    assert(LazyS.range_sum(li,ri,v) == S.range_sum(li,ri,v));
                }
            }
        }else if(t == 7){
            if(LazyS.count(l,r,v) != S.count(l,r,v)){
                assert(LazyS.count(l,r,v) == S.count(l,r,v));
            }
            if(S.count(l,r,v) > 0)assert(LazyS.maximum_freq(l,r,v) == S.maximum_freq(l,r,v));
        }else if(t == 8){
            assert(S.count(l,r,v) == LazyS.count(l,r,v));
            if(S.count(l,r,v) > 0)assert(LazyS.minimum_freq(l,r,v) == S.minimum_freq(l,r,v));
        }else if(t == 9){
            vpll qrs;
            int u = rand()%10000 + 1;
            for(int i = l ; i < r ; i++)qrs.emplace_back(i,u);
            S.set_together(qrs,v);
            LazyS.uniform_insert(l,r,u,v);
        }else if(t == 10 ){
            vpll qrs;
            int u = rand()%10000 + 1;
            for(int i = l ; i < r ; i++)qrs.emplace_back(i,u);
            S.insert_together(qrs,v);
            LazyS.range_insert(l,r,u,v);
        }else if(t == 11){
            int v2 = rand()%(S.version()+1);
            vpll qrs;
            for(int i = l ; i < r ; i++)qrs.emplace_back(i,S.count(i,v));
            S.set_together(qrs,v2);
            LazyS.test_rangecp(l,r,v,v2);
            assert(S.version() == LazyS.version());
        }
        if(testcnt%100 == 0){
            vpll qrs;
            for(int i = Llim ; i <= Rlim ; i++)qrs.emplace_back(i,0);
            S.set_together(qrs,v);
            LazyS.uniform_insert(Llim,Rlim+1,0,v);
        }
        if(testcnt%10000 == 0){
            cerr << "OK : rem = " << testcnt << endl;
        }
    }
};

int main(){
    test_persistent_datastructure();
}