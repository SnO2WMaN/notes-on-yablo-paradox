#import "template.typ": *
#import "@preview/equate:0.2.1": equate

#set math.equation(numbering: "(1.i)")
#show: equate.with(breakable: true, sub-numbering: true, number-mode: "label")

#show: project.with(
  title: "Yabloのパラドックスについて",
  authors: ("SnO2WMaN",),
)

= はじめに

文 $G$ が「$G$ は正しくない」という主張だとする．この主張は決定不能，つまり正しいか正しくないかを決めることは出来ない．
これは嘘つきのパラドックスとして知られているが，$G$ は $G$ 自身の真偽について述べているので自己言及をしていると考えられる．

では，自己言及をしなければこうした事態は発生しないのか？
Yabloのパラドックスは，自己言及をしない（ように見える）文であっても，真偽が決定不能となる一例を示すものである．

ところで，Gödelの不完全性定理の根幹となるアイデアは，非常に荒く言えば，
真偽という概念を理論上の証明可能性として捉え直して嘘つきのパラドックスを形式化することである．
このアイデアをYabloのパラドックスに適用することで，Yabloのパラドックスを形式化し，不完全性定理を導くことが出来る．

= Yabloのパラドックス <sect:intro_yablo_paradox>

Yabloのパラドックス @yabloParadoxSelfReference1993 を説明する．
このパラドックスは，一見して自己言及をしない命題であっても，その命題の真偽は決定不能となる一例を示すものである．

#remark[
  ここでは，真偽という概念を大雑把に用いる．
]

#definition[
  無限個の文 $Y_0, Y_1, ...$ を考える．

  ただし，$i in omega$ とし，各 $Y_i$ は「任意の $i < j$ について $Y_j$ は正しくない」という主張である．
]

#remark[
  $Y_i$ は $Y_i$ 自身の真偽については何も触れず，あくまで自分以降の文 $Y_(i+1), Y_(i+2),...$ の真偽について述べているだけなので，自己言及はしていないと考えられている．
  この考え方の是非は後の章で検討することにする．
]

#theorem[
  このとき，任意の $i in omega$ に対して $Y_i$ の真偽は決定できない．
] <thm:unformalized_yablo>

#proof[
  もし，ある文 $Y_i$ が正しいとする．
  すると，この文以降の文 $Y_(i + 1), Y_(i + 2),...$ はすべて正しくない．
  特に $Y_(i + 1)$ が正しくないとすると，$Y_(i + 1)$ 以降の文 $Y_(i + 2), Y_(i + 3),...$ の少なくともどれかは正しくなければならない．
  よって $Y_(i + 2), Y_(i + 3), ...$ のどれかに，正しく，かつ，正しくない文が存在して，これは明らかにおかしい．

  よって，任意の $Y_i$ は正しくないと考える．
  しかしこの場合でも，上記の議論より $Y_(i + 1), ...$ のどこかには正しい文が存在することになり，これもおかしい．
]

= Yabloのパラドックスの形式化 <sect:formalization_yablo_paradox>

@sect:intro_yablo_paradox の「正しくない」という概念を，証明可能性によって捉えることで，Yabloのパラドックスを形式化する．
この章は主に@cieslinskiGodelizingYabloSequence2013, @kikuchiThreeShortStories2011 を参考にした．

#let PeanoArithmetic = $bold(upright("PA"))$
#let Pr(T) = $upright("Pr")_#T$
#let Numeral(n) = $overline(#n)$

#notation[
  - 論理式として算術の論理式を考えていることにする．
  - $T$ は $PeanoArithmetic$ の適当な無矛盾な拡大とする．
  - $Pr(T)(x)$ は導出可能性条件をすべて満たす標準的な証明可能性述語であるとする．
]


#theorem[一般化された不動点定理 @boolosLogicProvability1994[pp.53]][
  任意の自由変数が $x, y$ のみの論理式 $phi(x, y)$ に対して，次のような自由変数が $x$ だけの論理式 $psi(x)$ が存在し，その算術的階層は等しい．
  $
    PeanoArithmetic vdash forall x. [psi(x) <-> phi(x, GoedelNum(psi))]
  $
  $psi(x)$ を $phi(x, y)$ の不動点という．
] <thm:generalized_fixpoint_theorem>

#let apply = $upright("apply")$
#let Yablo(T, n) = $upright("Y")_#T (#n)$

#definition[Yablo文][
  まず $phi(x, y)$ を次のように定義する．
  $
    phi(x, y) :equiv forall z. [x < z -> not Pr(T)(apply(y, z))]
  $
  ただし，$apply(y, z)$ は，$psi(v)$ を自由変数が $v$ だけの論理式，$n in omega$ として，$apply(GoedelNum(psi(v)), Numeral(n)) = GoedelNum(psi(Numeral(n)))$ を満たす関数とする．

  @thm:generalized_fixpoint_theorem によって得られる $phi(x, y)$ の不動点 $Yablo(T, x)$ について，
  $n in omega$ に対して $Yablo(T, Numeral(n))$ を $T$ の $n$ 番目の Yablo文とする．
]

#notation[
  表記の煩雑さを避けるため，以降では自然数 $n in omega$ とその数項 $Numeral(n)$ とを区別しない．
  つまり，$Yablo(T, Numeral(n))$ を $Yablo(T, n)$ と書いたりすることにする．
]

#remark[
  $T$ のYablo文の算術的階層は $Pr(T)(x)$ と同じである．普通，$Pr(T)(x)$ は $Sigma_1$ として取れるので，Yablo文も $Sigma_1$ とする．
]

#remark[
  展開すれば，$Yablo(T, n)$ は以下を満たす．
  $
    PeanoArithmetic vdash forall x. [Yablo(T, x) <-> forall z. [x < z -> not Pr(T)(GoedelNum(Yablo(T, z))))]] #<eq:yablo_def>
  $

  つまり，任意の $n$ について，$n$ 番目のYablo文 $Yablo(T, n)$ は「$n$ 番目以降の全てのYablo文 $Yablo(T, n + 1), Yablo(T, n + 2), ...$ は $T$ 上で証明できない」ことを表しており，
  これは @sect:intro_yablo_paradox で述べたYabloの文を $T$ 上の証明可能性によって形式化したものとして考えることが出来る．
]

#let D1 = $bold("D1")$
#let D2 = $bold("D2")$
#let D3 = $bold("D3")$

さて，このように定義したYablo文から，第1不完全性定理を出すことが出来る．
証明は，@thm:unformalized_yablo での証明の議論と同じような議論で行われる．

#lemma[
  $T$ が無矛盾なら，任意の $n in omega$ について $T nvdash Yablo(T, n)$．
] <lem:G1_yablo_1>
#proof[
  ある $n in omega$ で $T vdash Yablo(T, n)$ と仮定する．

  @eq:yablo_def から，$ T vdash forall z. [n < z -> not Pr(T)(GoedelNum(Yablo(T, z)))] #<eq:G1_yablo_1:def_s> $

  @eq:G1_yablo_1:def_s で，$z = n + 1$ として取れば，$ T vdash not Pr(T)(GoedelNum(Yablo(T, n + 1))) #<eq:G1_yablo_1:not_sn> $

  また @eq:G1_yablo_1:def_s から算術的な計算によって $T vdash forall z. [n + 1 < z -> not Pr(T)(GoedelNum(Yablo(T, z)))]$ も言えて，
  これは @eq:yablo_def から $T vdash Yablo(T, n + 1)$ が言える．導出可能性条件 $D1$ より，
  $
    T vdash Pr(T)(GoedelNum(Yablo(T, n + 1)))
  $ <eq:G1_yablo_1:sn>

  @eq:G1_yablo_1:def_s と @eq:G1_yablo_1:not_sn から $T vdash bot$ が出せる．しかし $T$ は無矛盾なのでこれはおかしい．
]

#let Model(M) = $frak(#M)$
#let StandardModel = $frak(N)$

#lemma[
  $T$ が $Sigma_1$-健全なら，任意の $n in omega$ について $T nvdash not Yablo(T, n)$．
] <lem:G1_yablo_2>
#proof[
  ある $n in omega$ で $T vdash not Yablo(T, n)$ と仮定する．

  すると，@eq:yablo_def から $T vdash exists z. [n < z and Pr(T)(GoedelNum(Yablo(T, z)))]$ が言える．
  $T$ の $Sigma_1$-健全性から $StandardModel$ を経由して，適当な $m in omega$ が取れて $T vdash Pr(T)(GoedelNum(Yablo(T, m)))$．

  再び $Sigma_1$-健全性から $T vdash Yablo(T, m)$ が言える．しかし @lem:G1_yablo_1 からこれはおかしい．
]

@lem:G1_yablo_1 と @lem:G1_yablo_2 より，直ちに@cor:G1_yablo が成り立つ．

#theorem[Gödelの第1不完全性定理][
  $T$ が $Sigma_1$-健全なら，$T$ の任意のYablo文 $Yablo(T, n)$ は決定不能であり，したがって $T$ は不完全である．
]<cor:G1_yablo>

では，第2不完全性定理についてはどうなるのか？
これに関しては，@thm:eqv_yablo_con が成り立ち．これと@cor:G1_yablo から直ちに従う．

#definition[
  $T$ の無矛盾性を表す文 $Con(T) :equiv not Pr(T)(GoedelNum(bot))$ とする．
]

#lemma[@KurahashiShomeikanoseironri2016[補題4.2.4]][
  $U$ を $PeanoArithmetic$ の適当な拡大理論としたとき，任意の文 $sigma$ に対して，次は同値．
  1. $U vdash Con(T) -> not Pr(T) (GoedelNum(sigma))$
  2. $U vdash Pr(T) (GoedelNum(sigma)) -> Pr(T) (GoedelNum(not sigma))$
]<lem:eqv_yablo_con:lem1>

任意のYablo文は，$T$ の形式的無矛盾性と同値である．

#theorem[
  $T vdash forall x.[Yablo(T, x) <-> Con(T)]$
]<thm:eqv_yablo_con>
#proof[
  全称化より，適当な $n in omega$ に対して $T vdash Yablo(T, n) <-> Con(T)$ を示せば十分．
  #struct[
    $T vdash Yablo(T, n) -> Con(T)$ を示す．
    $
      T &vdash bot -> Yablo(T, n + 1) & #text[爆発律] \
        &vdash Pr(T)(GoedelNum(bot)) -> Pr(T)(GoedelNum(Yablo(T, n + 1))) & #text[$D1$, $D2$] \
        &vdash not Pr(T)(GoedelNum(Yablo(T, n + 1))) -> Con(T) #<eq:eqv_yablo_con:1:1> \
      T &vdash Yablo(T, n) -> not Pr(T)(GoedelNum(Yablo(T, n + 1))) &  #text[@eq:yablo_def より] #<eq:eqv_yablo_con:1:2> \
      T &vdash Yablo(T, n) -> Con(T) &  #text[@eq:eqv_yablo_con:1:1, @eq:eqv_yablo_con:1:2 より]
    $
  ]

  #struct[
    $T vdash Con(T) -> Yablo(T, n)$ を示す．
    $
      T &vdash Yablo(T, n) -> Yablo(T, n + 1) \
        &vdash Pr(T)(GoedelNum(Yablo(T, n))) -> Pr(T)(GoedelNum(Yablo(T, n + 1))) & #text[$D1$, $D2$] #<eq:eqv_yablo_con:2:1> \
      T &vdash Yablo(T, n) -> not Pr(T)(GoedelNum(Yablo(T, n + 1))) & #text[@eq:yablo_def より] \
        &vdash Pr(T)(GoedelNum(Yablo(T, n + 1))) -> not Yablo(T, n) #<eq:eqv_yablo_con:2:2> \
      T &vdash Pr(T)(GoedelNum(Yablo(T, n))) -> not Yablo(T, n) & #text[@eq:eqv_yablo_con:2:1 と @eq:eqv_yablo_con:2:2 より] \
        &vdash Pr(T)(GoedelNum(Pr(T)(GoedelNum(Yablo(T, n))))) ->  Pr(T)(GoedelNum(not Yablo(T, n))) & #text[$D1$, $D2$] #<eq:eqv_yablo_con:2:3> \
      T &vdash Pr(T)(GoedelNum(Yablo(T, n))) -> Pr(T)(GoedelNum(Pr(T)(GoedelNum(Yablo(T, n))))) & #text[$D3$] #<eq:eqv_yablo_con:2:4> \
      T &vdash Pr(T)(GoedelNum(Yablo(T, n))) -> Pr(T)(GoedelNum(not Yablo(T, n))) & #text[@eq:eqv_yablo_con:2:3, @eq:eqv_yablo_con:2:4 より] \
        &vdash Con(T) -> not Pr(T)(GoedelNum(Yablo(T, n))) & #text[@lem:eqv_yablo_con:lem1 より] \
        &vdash forall x. [Con(T) -> not Pr(T)(GoedelNum(Yablo(T, x)))] & #text[全称化] \
        &vdash Con(T) -> forall x. [not Pr(T)(GoedelNum(Yablo(T, x)))] \
        &vdash Con(T) -> Yablo(T, n) & #text[@eq:yablo_def より]
    $
  ]
]

#theorem[Gödelの第2不完全性定理][
  $T$ が無矛盾なら $T nvdash Con(T)$．
  また，$T$ が $Sigma_1$-健全なら $T nvdash not Con(T)$．
]<cor:G2_yablo>

また，@thm:eqv_yablo_con から，次の@cor:eqv_yablo_arbitary が従う．

#corollary[
  $T vdash forall x, y. [Yablo(T, x) <-> Yablo(T, y)]$．
] <cor:eqv_yablo_arbitary>

#remark[
  元々のYabloのパラドックスとの類推を考えると，$Y_0$ とは「$Y_1, Y_2, ...$ は正しくない」と述べているはずの命題であるので，
  $T + Yablo(T, 0) nvdash Yablo(T, 1)$ であってほしい．
  しかし，@cor:eqv_yablo_arbitary を更に変形することで $T + Yablo(T, 0) vdash Yablo(T, 1)$ が言えるため，これは成り立たない．
]


#let Goedel(T) = $upright("G")_#T$

最後にGödel文について書いておく．
Gödel文と $Con(T)$ は $T$ 上で同値であるという事実が成り立つ．
この事実から，任意のYablo文とGödel文との同値性(@cor:eqv_goedel_yablo)も得られる．

#definition[
  $T$ のGödel文 $Goedel(T)$ は $Pr(T)(x)$ の不動点とする．
]

#proposition[@KurahashiShomeikanoseironri2016[命題4.2.6]][
  $T vdash Goedel(T) <-> Con(T)$．
]<thm:eqv_goedel_con>

#corollary[
  $T vdash forall x. [Goedel(T) <-> Yablo(T, x)]$．
]<cor:eqv_goedel_yablo>

通常の通り，$Goedel(T)$ によって第1不完全性定理と第2不完全性定理が成り立つため，
@cor:eqv_goedel_yablo から @cor:G1_yablo と @cor:G2_yablo が直ちに従う．
その意味では@thm:eqv_yablo_con 以外の定理はそれほどおもしろい結果でもないかもしれない．
