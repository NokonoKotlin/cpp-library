# UnionFind を SplayTree で書いたやつ

ただの UnionFind。rollback もついてる。

### 注意点
UF 木をマージするデータ構造であり、辺をつなげると捉えるとバグる。  
unite(u,v) で u , v の属する UF 木が同じ場合はそもそも unite を呼び出さず、rollback にもストックされない。  


## ライセンス
掲載したソースコードは MIT ライセンス (https://opensource.org/licenses/mit-license.php) で公開しています。ソースコードのコメントにライセンスが指示する条件 (以下 $2$ 点) を書いてあるので、消さずに使用してください。

- 著作者の表示
- ライセンスの全文またはライセンスの原文が掲載されたページへのリンク


### 概要
- SplayTree で UnionFind を実装。ノードに対応する SplayNode* を用意する。
- unite(u,v) するときは  u,v それぞれが属する SplayTree を merge する。
- x が属する連結成分の代表頂点(UF でいうところの root) は、x が属する SplayTree で最も左の頂点
    - left[x] := x よりも左にあるノード。ただし、どれかはわからない。
    - left[x] を経路圧縮することで、目的の leftmost(x) を得られる。
    - これは splay を減らす工夫で、UnionFind の経路圧縮と同じ。
    - rollback が必要な場合は経路圧縮せずに x から可能な限り上にのぼり、可能な限り左に降りて logN で計算
        - rollback があるとまあ少し遅い
- UF と同じ機能だけを使いたい場合は unite&rollback 以外は splay する必要がなく速い。
- 実装/設計 について
    - 頂点が持つ値を使用する場合は、通常の splay 木と同程度と考えれば OK
    - splay する場面としない場面があるので、編集する際は注意