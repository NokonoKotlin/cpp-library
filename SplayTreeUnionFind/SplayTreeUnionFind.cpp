#include<iostream>
#include<vector>
#include<cassert>
#include<stack>
using std::pair;
using std::stack;
using std::vector;
/*
    Copyright ©️ (c) NokonoKotlin (okoteiyu) 2024. 
    Released under the MIT license(https://opensource.org/licenses/mit-license.php) 
*/
template<class T , bool _rollback_ = false>
class SplayUnionFind{
    struct SplayNode{
        SplayNode *parent = nullptr;SplayNode *left = nullptr;SplayNode *right = nullptr;
        T Value;
        T Min,Max,Sum;
        int Nodeid;
        int SubTreeSize = 1;
        pair<bool,pair<T,T> > lazy_affine ={false , {T(),T()}};
        void set_lazyAffine(T& a, T& b){
            if(this->lazy_affine.first)this->lazy_affine.second = { a*this->lazy_affine.second.first , a*this->lazy_affine.second.second + b};
            else this->lazy_affine = {true , {a,b}};
        }
        pair<bool,T> lazy_update = {false,T()};
        void set_lazyUpdate(T &x){
            this->lazy_update.first = true;
            this->lazy_update.second=x;
            this->lazy_affine.first = false;
        }
        SplayNode(){}
        SplayNode(T val){Value = val;update();}
        void update(){
            this->eval();
            this->Sum = this->Max = this->Min = this->Value;
            this->SubTreeSize = 1;
            if(bool(this->left)){
                this->left->eval();
                this->SubTreeSize += this->left->SubTreeSize;
                if(this->left->Min < this->Min)this->Min = this->left->Min;
                if(this->left->Max > this->Max)this->Max = this->left->Max;
                this->Sum += this->left->Sum;
            }
            if(bool(this->right)){
                this->right->eval();
                this->SubTreeSize += this->right->SubTreeSize;
                if(this->right->Min < this->Min)this->Min = this->right->Min;
                if(this->right->Max > this->Max)this->Max = this->right->Max;
                this->Sum += this->right->Sum;
            }
            return;
        }
        void eval(){
            if(this->lazy_update.first){
                this->Value = this->Min = this->Max = this->lazy_update.second;
                this->Sum = (this->lazy_update.second)*(this->SubTreeSize);
                if(bool(this->left))this->left->set_lazyUpdate(this->lazy_update.second);
                if(bool(this->right))this->right->set_lazyUpdate(this->lazy_update.second);
                this->lazy_update.first = false;
            }
            if(this->lazy_affine.first){
                this->Value = this->lazy_affine.second.first * this->Value + this->lazy_affine.second.second;
                this->Min = this->lazy_affine.second.first * this->Min + this->lazy_affine.second.second;
                this->Max = this->lazy_affine.second.first * this->Max + this->lazy_affine.second.second;
                this->Sum = this->lazy_affine.second.first * this->Sum + this->SubTreeSize*this->lazy_affine.second.second;
                if(bool(this->left))this->left->set_lazyAffine(this->lazy_affine.second.first,this->lazy_affine.second.second);
                if(bool(this->right))this->right->set_lazyAffine(this->lazy_affine.second.first,this->lazy_affine.second.second);
                this->lazy_affine.first = false;
            }
        }
        void rotate(){
            if(this->parent->parent){if(this->parent == this->parent->parent->left)this->parent->parent->left = this;else this->parent->parent->right = this; }
            this->parent->eval();this->eval();
            if(this->parent->left == this){
                this->parent->left = this->right;if(this->right)this->right->parent = this->parent;
                this->right = this->parent;this->parent = this->right->parent;
                this->right->parent = this;this->right->update();
            }else{
                this->parent->right = this->left;if(this->left)this->left->parent = this->parent;
                this->left = this->parent;this->parent = this->left->parent;
                this->left->parent = this;this->left->update();
            }this->update();
        }
        int state(){if(this->parent == nullptr)return 0;if(this->parent->left == this)return 1;return 2;}
        void splay(){
            while(bool(this->parent)){if(this->parent->state() == 0){this->rotate();break;}
                if( this->parent->state() == this->state() )this->parent->rotate();else this->rotate();this->rotate();
            }this->update();
        }
    };
    stack<int> history;
    vector<SplayNode*> SplayUFNode;
    vector<int> left;
    int leftmost(int x){
        if(_rollback_){
            SplayNode* now = SplayUFNode[x];
            now->splay();
            while(now->left != nullptr)now = now->left;
            now->splay();
            return now->Nodeid;
        }
        if(left[x] == x)return x;
        return left[x] = leftmost(left[x]);
    }
    public:
    SplayUnionFind(int N , T init_){
        vector<SplayNode*>(N).swap(SplayUFNode);
        vector<int>(N).swap(left);
        for(int i = 0 ; i < N ; i++){
            SplayUFNode[i] = new SplayNode(init_);
            left[i] = i;
            SplayUFNode[i]->Nodeid = i;
        }
    }
    int root(int x){return leftmost(x);}
    bool same(int u , int v){return bool(root(u) == root(v));}
    bool unite(int u , int v){
        if(same(u,v))return false;
        u = leftmost(u);
        v = leftmost(v);
        SplayUFNode[u]->splay();
        SplayNode* rig = SplayUFNode[v];
        rig->splay();
        if(_rollback_)history.push(rig->Nodeid);
        SplayUFNode[u]->parent = rig;
        rig->left = SplayUFNode[u];
        rig->update();
        left[rig->Nodeid] = leftmost(u);
        left[v] = leftmost(u);
        return true;
    }
    bool rollback(){
        assert(_rollback_);
        if(history.empty())return false;
        int last = history.top();history.pop();
        SplayUFNode[last]->splay();
        SplayUFNode[last]->left->parent = nullptr;
        SplayUFNode[last]->left = nullptr;
        SplayUFNode[last]->update();
        return true;
    }
    vector<int> member(int x){
        vector<int> res;
        SplayUFNode[x]->splay();
        stack<SplayNode*> st;
        st.push(SplayUFNode[x]);
        while(!st.empty()){
            SplayNode* now = st.top();st.pop();
            now->eval();
            res.push_back(now->Nodeid);
            if(now->left != nullptr)st.push(now->left);
            if(now->right != nullptr)st.push(now->right);
        }
        return res;
    }
    int size(int x){SplayUFNode[x]->splay();return SplayUFNode[x]->SubTreeSize;}
    T value(int x){SplayUFNode[x]->splay();return SplayUFNode[x]->Value;}
    void set(int x , T y){SplayUFNode[x]->splay();SplayUFNode[x]->Value = y;SplayUFNode[x]->update();}
    T sum(int x){SplayUFNode[x]->splay();return SplayUFNode[x]->Sum;}
    T min(int x){SplayUFNode[x]->splay();return SplayUFNode[x]->Min;}
    T max(int x){SplayUFNode[x]->splay();return SplayUFNode[x]->Max;}
    void AllUpdate(int x , T y){SplayUFNode[x]->splay();SplayUFNode[x]->set_lazyUpdate(y);}
    void AllAffine(int x , T a , T b){SplayUFNode[x]->splay();SplayUFNode[x]->set_lazyAffine(a,b);}
    void AllAdd(int x , T y){AllAffine(x,1,y);}
    /*
        Copyright ©️ (c) NokonoKotlin (okoteiyu) 2024. 
        Released under the MIT license(https://opensource.org/licenses/mit-license.php) 
    */
};