#include <iostream>
#include <vector>
#include <cassert>
using namespace std;
/*   
    Copyright ©️ (c) NokonoKotlin (okoteiyu) 2024.
    Released under the MIT license(https://opensource.org/licenses/mit-license.php) 
*/
template<class T, class F >
class ExtendedArray{
    private:
    struct SplayNode{
        SplayNode *parent = nullptr;
        SplayNode *left = nullptr;
        SplayNode *right = nullptr;
        T R;
        T L;
        T length(){return R-L;}
        T length_sum;
        F Value;
        F Sum;
        F Min;
        F Max;
        int SubTreeSize = 1;
        private:
        bool copied_instance = false;
        public:
        SplayNode copy(){
            assert(copied_instance == false);
            SplayNode res = *this;
            res.left = nullptr;
            res.right = nullptr;
            res.parent = nullptr;
            res.copied_instance = true;
            return res;
        }
        pair<bool,pair<F,F> > lazy_affine ={false , {F(),F()}};
        void set_lazyAffine(F& a, F& b){
            if(this->lazy_affine.first)this->lazy_affine.second = { a*this->lazy_affine.second.first , a*this->lazy_affine.second.second + b};
            else this->lazy_affine = {true , {a,b}};
        }
        pair<bool,T> lazy_shift = {false,T()};
        void set_lazyShift(T x){
            if(this->lazy_shift.first)lazy_shift.second += x;
            else lazy_shift.second = x;
            this->lazy_shift.first = true;
        }
        SplayNode(){}
        SplayNode(T l , T r , F Value_){
            assert(l < r);
            R = r;
            L = l;
            Value = Value_;
            update();
        }
        void rotate(){
            if(this->parent->parent != nullptr){
                if(this->parent == this->parent->parent->left)this->parent->parent->left = this;
                else this->parent->parent->right = this;
            }
            this->parent->eval();
            this->eval();
            if(this->parent->left == this){
                this->parent->left = this->right;
                if(this->right != nullptr)this->right->parent = this->parent;
                this->right = this->parent;
                this->parent = this->right->parent;
                this->right->parent = this;
                this->right->update();
            }else{
                this->parent->right = this->left;
                if(this->left != nullptr)this->left->parent = this->parent;
                this->left = this->parent;
                this->parent = this->left->parent;
                this->left->parent = this;
                this->left->update();
            }
            this->update();
            return;
        }
        int state(){
            if(this->parent == nullptr)return 0;
            this->parent->eval();
            if(this->parent->left == this)return 1;
            else if(this->parent->right == this)return 2;
            return 0;
        }
        void splay(){
            while(this->parent != nullptr){
                if(this->parent->state() == 0){
                    this->rotate();
                    break;
                }
                if( this->parent->state() == this->state() )this->parent->rotate();
                else this->rotate();
                this->rotate();
            }
            this->update();
            return;
        }
        void update(){
            assert(copied_instance == false);
            this->eval();
            this->SubTreeSize = 1;
            this->length_sum = this->length();
            this->Min = this->Value;
            this->Max = this->Value;
            this->Sum = this->Value*this->length();
            if(this->left != nullptr){
                this->left->eval();
                this->SubTreeSize += this->left->SubTreeSize;
                this->length_sum += this->left->length_sum;
                if(this->left->Min < this->Min)this->Min = this->left->Min;
                if(this->left->Max > this->Max)this->Max = this->left->Max;
                this->Sum += this->left->Sum;
            }
            if(this->right != nullptr){
                this->right->eval();
                this->SubTreeSize += this->right->SubTreeSize;
                this->length_sum += this->right->length_sum;
                if(this->right->Min < this->Min)this->Min = this->right->Min;
                if(this->right->Max > this->Max)this->Max = this->right->Max;
                this->Sum += this->right->Sum;
            }
            return;
        }
        void eval(){
            assert(copied_instance == false);
            if(this->lazy_affine.first){
                this->Value = this->lazy_affine.second.first * this->Value + this->lazy_affine.second.second;
                this->Min = this->lazy_affine.second.first * this->Min + this->lazy_affine.second.second;
                this->Max = this->lazy_affine.second.first * this->Max + this->lazy_affine.second.second;
                this->Sum = this->lazy_affine.second.first * this->Sum + (this->length_sum)*this->lazy_affine.second.second;
                if(this->Max < this->Min)swap(this->Max,this->Min);
                if(this->left != nullptr)this->left->set_lazyAffine(this->lazy_affine.second.first,this->lazy_affine.second.second);
                if(this->right != nullptr)this->right->set_lazyAffine(this->lazy_affine.second.first,this->lazy_affine.second.second);
                this->lazy_affine.first = false;
            }
            if(this->lazy_shift.first){
                this->L += this->lazy_shift.second;
                this->R += this->lazy_shift.second;
                if(this->left != nullptr)this->left->set_lazyShift(this->lazy_shift.second);
                if(this->right != nullptr)this->right->set_lazyShift(this->lazy_shift.second);
                this->lazy_shift.first = false;
            }
        }
    };
    inline static constexpr bool CompareNode(SplayNode *a , SplayNode *b){return a->R <= b->R;}
    SplayNode *get_sub(int index , SplayNode *root){
        if(bool(root)==false)return root;
        SplayNode *now = root;
        while(true){
            now->eval();
            int left_size = 0;
            if(now->left != nullptr)left_size = now->left->SubTreeSize;
            if(index < left_size)now = now->left;
            else if(index == left_size)break;
            else{
                now = now->right;
                index = index - left_size-1;
            }
        }
        now->splay();
        return now;
    }
    SplayNode *merge(SplayNode *leftRoot , SplayNode *rightRoot){
        if(leftRoot!=nullptr)leftRoot->update();
        if(rightRoot!=nullptr)rightRoot->update();
        if(leftRoot == nullptr)return rightRoot;
        if(rightRoot == nullptr)return leftRoot;
        rightRoot = get_sub(0,rightRoot);
        rightRoot->left = leftRoot;
        leftRoot->parent = rightRoot;
        rightRoot->update();
        return rightRoot;
    }
    std::pair<SplayNode*,SplayNode*> split(int leftnum, SplayNode *root){
        if(leftnum<=0)return std::make_pair(nullptr , root);
        if(leftnum >= root->SubTreeSize)return std::make_pair(root, nullptr);
        root = get_sub(leftnum , root);
        SplayNode *leftRoot = root->left;
        SplayNode *rightRoot = root;
        if(rightRoot != nullptr)rightRoot->left = nullptr;
        if(leftRoot != nullptr)leftRoot->parent = nullptr;
        leftRoot->update();
        rightRoot->update();
        return std::make_pair(leftRoot,rightRoot);
    }
    std::pair<SplayNode*,int> bound_sub(SplayNode* Node , SplayNode *root , bool lower){
        if(root == nullptr)return std::make_pair(root,0);
        SplayNode *now = root;
        Node->update();
        bool satisfy = false;
        while(true){
            now->eval();
            if(lower)satisfy = !CompareNode(Node,now);
            else satisfy = CompareNode(now,Node);
            if(satisfy == true && now->right != nullptr)now = now->right;
            else if(satisfy == false && now->left != nullptr)now = now->left;
            else break;
        }
        int res = 0;
        if(satisfy)res = 1;
        now->splay();
        if(now->left != nullptr)res += now->left->SubTreeSize;
        return std::make_pair(now ,res);
    }
    pair<int,int> modify(T i){
        if(i == leftmost)return {-1,0};
        if(i == rightmost)return {SplayTreeSize()-1,SplayTreeSize()};
        assert(leftmost < i && i < rightmost);
        int it_ = lower_bound(i);
        m_Root = get_sub(it_,m_Root);
        m_Root->update();
        if(i == m_Root->L)return {it_-1,it_};
        if( i < m_Root->R ){
            T nR = m_Root->R;
            F V = m_Root->Value;
            m_Root->R = i;
            m_Root->update();
            SplayNode* nnd = new SplayNode(i,nR,V);
            nnd->update();
            m_Root = bound_sub(nnd,m_Root,true).first;
            if(!CompareNode(nnd , m_Root)){
                if(m_Root->right != nullptr)m_Root->right->parent = nnd;
                nnd->right = m_Root->right;
                m_Root->right = nullptr;
                nnd->left = m_Root;
            }else{
                if(m_Root->left != nullptr)m_Root->left->parent = nnd;
                nnd->left = m_Root->left;
                m_Root->left = nullptr;
                nnd->right = m_Root;
            }
            m_Root->parent = nnd;
            m_Root->update();
            nnd->update();
            m_Root = nnd;
        }
        return {it_,it_+1};
    }
    int SplayTreeSize(){if(m_Root==nullptr)return 0;return m_Root->SubTreeSize;}
    int lower_bound(T x){
        if(SplayTreeSize() == 0)return 0;
        std::pair<SplayNode*,int> tmp = bound_sub(BluffObject(leftmost,x,F(0)),m_Root,true);
        m_Root = tmp.first;
        return tmp.second;
    }
    int upper_bound(T x){
        if(SplayTreeSize() == 0)return 0;
        std::pair<SplayNode*,int> tmp = bound_sub(BluffObject(leftmost,x,F(0)),m_Root,false);
        m_Root = tmp.first;
        return tmp.second;
    }
    SplayNode *m_Root = nullptr;
    inline static SplayNode* const m_bluff_object = new SplayNode();
    inline static SplayNode* const BluffObject(T l , T r , F f){
        m_bluff_object->L = l;
        m_bluff_object->R = r;
        m_bluff_object->Value = f;
        return m_bluff_object;
    }
    T leftmost ;
    T rightmost;
    void init(F init_value){
        assert(leftmost < rightmost);
        m_Root = new SplayNode(leftmost,rightmost,init_value);
    }
    void release(){
        while(SplayTreeSize()>0){
            pair<SplayNode*,SplayNode*> tmp = DeleteNode_sub(0,m_Root);
            m_Root = tmp.first;
            delete tmp.second;
        }
    }
    public:
    ExtendedArray(){}
    ExtendedArray(T leftmost_ , T rightmost_ ,F init_v):leftmost(leftmost_),rightmost(rightmost_){init(init_v);}
    ExtendedArray(const ExtendedArray<T,F> &x) = delete ;
    ExtendedArray& operator = (const ExtendedArray<T,F> &x) = delete ;
    ExtendedArray ( ExtendedArray<T,F>&& x){assert(0);}
    ExtendedArray& operator = ( ExtendedArray<T,F>&& x){assert(0);}
    void Reset(T leftmost_,T rightmost_ , F init_v){
        leftmost = leftmost_;
        rightmost = rightmost_;
        init(init_v);
    }
    T Llimit(){return leftmost;}
    T Rlimit(){return rightmost;}
    SplayNode get(int i){
        assert(0 <= i && i < size());
        m_Root = get_sub(i,m_Root);
        return m_Root->copy();
    }
    SplayNode GetRange(T lef , T rig){
        assert(leftmost <= lef && lef < rig && rig <= rightmost);
        int itl = modify(lef).second;
        int itr = modify(rig).second;
        std::pair<SplayNode*,SplayNode*> tmp = split(itr,m_Root);
        SplayNode* rightRoot = tmp.second;
        tmp = split(itl,tmp.first);
        SplayNode res = tmp.second->copy();
        m_Root = merge(merge(tmp.first,tmp.second),rightRoot);
        return res;
    }
    void circular_shift(T lef , T rig , T x){
        assert(leftmost <= lef && lef < rig && rig <= rightmost);
        if(abs(x) == rig - lef)return;
        if(x == T(0))return;
        if(x < 0)x = rig-lef+x;
        assert(0 < x && x < rig - lef);
        T mid = rig - x;
        int it_l = modify(lef).second;
        int it_m = modify(mid).second;
        int it_r = modify(rig).first;
        assert(0 <= it_l && it_l < it_m && it_m <= it_r && it_r < SplayTreeSize());
        pair<SplayNode*,SplayNode*> tmp = split(it_r+1 , m_Root);
        SplayNode* p4 = tmp.second;
        tmp = split(it_m,tmp.first);
        SplayNode* p3 = tmp.second;
        tmp = split(it_l,tmp.first);
        SplayNode* p2 = tmp.second;
        SplayNode* p1 = tmp.first;
        p2->set_lazyShift(x);
        p3->set_lazyShift(T(x-rig+lef));
        p2->update();
        p3->update();
        m_Root = merge(merge(merge(p1,p3),p2),p4);
    }
    void RPush(T lef , T rig , F x){
        assert(leftmost <= lef && lef < rig && rig <= rightmost);
        circular_shift(lef,rightmost,(rig - lef));
        RangeUpdate(lef,rig,x);
    }
    void LPush(T lef , T rig , F x){
        assert(leftmost <= lef && lef < rig && rig <= rightmost);
        circular_shift(leftmost,rig,-(rig - lef));
        RangeUpdate(lef,rig,x);
    }
    void LErase(T lef , T rig , F init_){
        assert(leftmost <= lef && lef < rig && rig <= rightmost);
        RangeUpdate(lef,rig,init_);
        circular_shift(lef,rightmost,-(rig-lef));
    }
    void RErase(T lef , T rig , F init_){
        assert(leftmost <= lef && lef < rig && rig <= rightmost);
        RangeUpdate(lef,rig,init_);
        circular_shift(leftmost,rig,(rig-lef));
    }
    void RangeAffine(T lef , T rig , F A , F B){
        assert(leftmost <= lef && lef < rig && rig <= rightmost);
        int itl = modify(lef).second;
        int itr = modify(rig).second;
        std::pair<SplayNode*,SplayNode*> tmp = split(itr,m_Root);
        SplayNode* t2 = tmp.second;
        tmp = split(itl,tmp.first);
        tmp.second->set_lazyAffine(A,B);
        tmp.second->update();
        m_Root = merge(merge(tmp.first,tmp.second),t2);
    }
    void RangeAdd(T lef , T rig , F x){
        assert(leftmost <= lef && lef < rig && rig <= rightmost);
        RangeAffine(lef,rig,F(1),x);
    }
    void RangeUpdate( T lef , T rig , F x){
        assert(leftmost <= lef && lef < rig && rig <= rightmost);
        RangeAffine(lef,rig,F(0),x);
        return;
    }
    F operator [](T x){
        assert(leftmost <= x && x < rightmost);
        if(x == leftmost)return get(0).Value;
        int it_ = upper_bound(x);
        return get(it_).Value;
    }
    T size(){return rightmost - leftmost;}
    void Debug(){
        cerr << "DEBUG" << endl;
        cerr << "L : " ;for(int i = 0 ; i < SplayTreeSize();i++)cerr << get(i).L << " ";cerr << endl;
        cerr << "R : " ;for(int i = 0 ; i < SplayTreeSize();i++)cerr << get(i).R << " ";cerr << endl;
        cerr << "V : " ;for(int i = 0 ; i < SplayTreeSize();i++)cerr << get(i).Value << " ";cerr << endl;
    }
    /*   
        Copyright ©️ (c) NokonoKotlin (okoteiyu) 2024.
        Released under the MIT license(https://opensource.org/licenses/mit-license.php) 
    */
};