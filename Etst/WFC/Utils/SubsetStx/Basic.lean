import Etst.WFC.Ch5_SubsethoodPS
import Etst.WFC.Utils.SubsetStx.MapFv

namespace Etst
open Expr


namespace DefList.SubsetStx
  variable {dl: DefList}
  
  def subIrL {l r}:
    dl.SubsetStx (ir l r) l
  :=
    irL subId
  
  def subIrR {l r}:
    dl.SubsetStx (ir l r) r
  :=
    irR subId
  
  def irCtxL {a b r}
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx (ir a r) b
  :=
    trans subIrL sub
  
  def irCtxR {a b l}
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx (ir l a) b
  :=
    trans subIrR sub
  
  def subIrCtxL {a b}:
    dl.SubsetStx (ir a b) a
  :=
    irCtxL subId
  
  def subIrCtxR {a b}:
    dl.SubsetStx (ir a b) b
  :=
    irCtxR subId
  
  def irLR {al ar bl br}
    (subL: dl.SubsetStx al bl)
    (subR: dl.SubsetStx ar br)
  :
    dl.SubsetStx (ir al ar) (ir bl br)
  :=
    irI subL.irCtxL subR.irCtxR
  
  def subIrSymm
    {l r: SingleLaneExpr}
  :
    dl.SubsetStx (ir l r) (ir r l)
  :=
    irI subIrR subIrL
  
  def irSymm {x l r}
    (sub: dl.SubsetStx x (ir l r))
  :
    dl.SubsetStx x (ir r l)
  :=
    sub.trans subIrSymm
  
  def irSymmCtx {l r b}
    (sub: dl.SubsetStx (ir l r) b)
  :
    dl.SubsetStx (ir r l) b
  :=
    trans subIrSymm sub
  
  def irMonoCtxL {a al ar b}
    (subA: dl.SubsetStx a al)
    (sub: dl.SubsetStx (ir al ar) b)
  :
    dl.SubsetStx (ir a ar) b
  :=
    trans (irLR subA subId) sub
  
  def irMonoCtxR {a al ar b}
    (subA: dl.SubsetStx a ar)
    (sub: dl.SubsetStx (ir al ar) b)
  :
    dl.SubsetStx (ir al a) b
  :=
    trans (irLR subId subA) sub
  
  def irCtxElimL {x a b}
    (bc: dl.SubsetStx (ir x a) b)
    (ab: dl.SubsetStx x a)
  :
    dl.SubsetStx x b
  :=
    trans (irI subId ab) bc
  
  def irCtxElimR {x a b}
    (bc: dl.SubsetStx (ir a x) b)
    (ab: dl.SubsetStx x a)
  :
    dl.SubsetStx x b
  :=
    trans (irI ab subId) bc
  
  
  def complIr {x a b}
    (sub: dl.SubsetStx (ir x a) (ir b b.compl))
  :
    dl.SubsetStx x a.compl
  :=
    complI (irL sub) (irR sub)
  
  def complElimIr {x a b}
    (sub: dl.SubsetStx (ir x a.compl) (ir b b.compl))
  :
    dl.SubsetStx x a
  :=
    complElim (irL sub) (irR sub)
  
  def pe {x a b}
    (sub: dl.SubsetStx x b)
    (subC: dl.SubsetStx x b.compl)
  :
    dl.SubsetStx x a
  :=
    complElim (irCtxL sub) (irCtxL subC)
  
  def subPe {a b}:
    dl.SubsetStx (ir b b.compl) a
  :=
    pe subIrCtxL subIrCtxR
  
  def dni {x a}
    (sub: dl.SubsetStx x a)
  :
    dl.SubsetStx x a.compl.compl
  :=
    complI (irCtxL sub) subIrR
  
  def dne {x a}
    (sub: dl.SubsetStx x a.compl.compl)
  :
    dl.SubsetStx x a
  :=
    complElim (irCtxL sub) (irCtxR (dni subId))
  
  def subDni {a}: dl.SubsetStx a (compl (compl a)) := dni subId
  def subDne {a}: dl.SubsetStx (compl (compl a)) a := dne subId
  
  def dniCtx {x a}
    (sub: dl.SubsetStx x a)
  :
    dl.SubsetStx (compl (compl x)) a
  :=
    trans subDne sub
  
  def dneCtx {x a}
    (sub: dl.SubsetStx (compl (compl x)) a)
  :
    dl.SubsetStx x a
  :=
    trans subDni sub
  
  def subCompl {a b}
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx b.compl a.compl
  :=
    let Sub := dl.SubsetStx (ir b.compl a)
    let subB: Sub b := trans subIrR sub
    let subBCompl: Sub b.compl := subIrL
    complI subB subBCompl
  
  def subComplElim {a b}
    (sub: dl.SubsetStx (compl a) (compl b))
  :
    dl.SubsetStx b a
  :=
    trans subDni (trans (subCompl sub) subDne)
  
  def complSwapCtx {a b}
    (sub: dl.SubsetStx (compl a) b)
  :
    dl.SubsetStx (compl b) a
  :=
    (subCompl sub).trans subDne
  
  def complSwap {a b}
    (sub: dl.SubsetStx a (compl b))
  :
    dl.SubsetStx b (compl a)
  :=
    subDni.trans (subCompl sub)
  
  
  def subNone {a}:
    dl.SubsetStx none a
  :=
    noneElim subId
  
  def subAny {x}:
    dl.SubsetStx x any
  :=
    complI (b := null) (noneElim subIrR) (noneElim subIrR)
  
  
  def mp {x a b}
    (xab: dl.SubsetStx x (impl a b))
    (xa: dl.SubsetStx x a)
  :
    dl.SubsetStx x b
  :=
    let nbnc := dni (irI (dni (irCtxL xa)) subIrCtxR)
    complElim (irCtxL xab) nbnc
  
  def implAbsorb {x a b}
    (xab: dl.SubsetStx x (impl a b))
  :
    dl.SubsetStx (ir x a) b
  :=
    mp (irCtxL xab) subIrR
  
  
  def subUnL {a b}:
    dl.SubsetStx a (un a b)
  :=
    complI subIrL (trans subIrR subIrL)
  
  def subUnR {a b}:
    dl.SubsetStx b (un a b)
  :=
    complI subIrL (trans subIrR subIrR)
  
  def unL {x a b}
    (sub: dl.SubsetStx x a)
  :
    dl.SubsetStx x (un a b)
  :=
    trans sub subUnL
  
  def unR {x a b}
    (sub: dl.SubsetStx x b)
  :
    dl.SubsetStx x (un a b)
  :=
    trans sub subUnR
  
  def unCtx {l r b}
    (ac: dl.SubsetStx l b)
    (bc: dl.SubsetStx r b)
  :
    dl.SubsetStx (un l r) b
  :=
    (subCompl (irI (subCompl ac) (subCompl bc))).trans subDne
  
  def em {x a}:
    dl.SubsetStx x (un a a.compl)
  :=
    trans subDni (subCompl subPe)
  
  def unCtxLR {al ar bl br}
    (subL: dl.SubsetStx al bl)
    (subR: dl.SubsetStx ar br)
  :
    dl.SubsetStx (un al ar) (un bl br)
  :=
    unCtx subL.unL subR.unR
  
  def subUnSymm {l r}:
    dl.SubsetStx (un l r) (un r l)
  :=
    unCtx subUnR subUnL
  
  def unElimCtxL {l r b}
    (sub: dl.SubsetStx (un l r) b)
  :
    dl.SubsetStx l b
  :=
    trans subUnL sub
  
  def unElimCtxR {l r b}
    (sub: dl.SubsetStx (un l r) b)
  :
    dl.SubsetStx r b
  :=
    trans subUnR sub
  
  def unSymm {x l r}
    (sub: dl.SubsetStx x (un l r))
  :
    dl.SubsetStx x (un r l)
  :=
    sub.trans subUnSymm
  
  def unSymmCtx {l r b}
    (sub: dl.SubsetStx (un l r) b)
  :
    dl.SubsetStx (un r l) b
  :=
    unCtx (unElimCtxR sub) (unElimCtxL sub)
  
  def unElimSub {x l r a}
    (sub: dl.SubsetStx x (un l r))
    (subL: dl.SubsetStx l a)
    (subR: dl.SubsetStx r a)
  :
    dl.SubsetStx x a
  :=
    sub.trans (unCtx subL subR)
  
  def unMonoSubL {x la lb r}
    (sub: dl.SubsetStx x (un la r))
    (subL: dl.SubsetStx la lb)
  :
    dl.SubsetStx x (un lb r)
  :=
    unElimSub sub (unL subL) subUnR
  
  def unMonoSubR {x l ra rb}
    (sub: dl.SubsetStx x (un l ra))
    (subR: dl.SubsetStx ra rb)
  :
    dl.SubsetStx x (un l rb)
  :=
    unElimSub sub subUnL (unR subR)
  
  def unElim {x l r a}
    (sub: dl.SubsetStx x (un l r))
    (subL: dl.SubsetStx (ir x l) a)
    (subR: dl.SubsetStx (ir x r) a)
  :
    dl.SubsetStx x a
  :=
    complElim
      (irI
        (complI
          (trans (irLR subIrL subId) subL)
          (irCtxL subIrR))
        (complI
          (trans (irLR subIrL subId) subR)
          (irCtxL subIrR)))
      (irCtxL sub)
  
  /-
    Useful for unions of more than two expressions. Usage:
    
    ```
      unElim abc aElim (unElimCont bElim cElim)
    ```
  -/
  def unElimCont {x l r a}
    (subL: dl.SubsetStx (ir x l) a)
    (subR: dl.SubsetStx (ir x r) a)
  :
    dl.SubsetStx (ir x (un l r)) a
  :=
    unElim
      subIrCtxR
      (trans (irLR subIrCtxL subId) subL)
      (trans (irLR subIrCtxL subId) subR)
  
  def unElimImpl {x l r a}
    (sub: dl.SubsetStx x (un l r))
    (subL: dl.SubsetStx x (impl l a))
    (subR: dl.SubsetStx x (impl r a))
  :
    dl.SubsetStx x a
  :=
    complElim
      (irI
        (complI
          (trans (irLR subIrL subId) (implAbsorb subL))
          (irCtxL subIrR))
        (complI
          (trans (irLR subIrL subId) (implAbsorb subR))
          (irCtxL subIrR)))
      (irCtxL sub)
  
  
  def irUnDistL {x a b c}
    (sub: dl.SubsetStx x (ir (un a b) c))
  :
    dl.SubsetStx x (un (ir a c) (ir b c))
  :=
    (irL sub).unElim
      (unL (irSymm (irLR (irR sub) subId)))
      (unR (irSymm (irLR (irR sub) subId)))
  
  def irUnDistR {x a b c}
    (sub: dl.SubsetStx x (ir c (un a b)))
  :
    dl.SubsetStx x (un (ir c a) (ir c b))
  :=
    (irR sub).unElim
      (unL (irLR (irL sub) subId))
      (unR (irLR (irL sub) subId))
  
  def subIrUnDistElimL {a b c}:
    dl.SubsetStx
      (un (ir a c) (ir b c))
      (ir (un a b) c)
  :=
    unCtx
      (irI (irCtxL subUnL) subIrR)
      (irI (irCtxL subUnR) subIrR)
  
  def subIrUnDistElimR {a b c}:
    dl.SubsetStx
      (un (ir a b) (ir a c))
      (ir a (un b c))
  :=
    unCtx
      (irI subIrL (irCtxR subUnL))
      (irI subIrL (irCtxR subUnR))
  
  def subUnIrDistL {a b c}:
    dl.SubsetStx
      (un (ir a b) c)
      (ir (un a c) (un b c))
  :=
    unCtx
      (irLR subUnL subUnL)
      (irI subUnR subUnR)
  
  def subUnIrDistR {a b c}:
    dl.SubsetStx
      (un a (ir b c))
      (ir (un a b) (un a c))
  :=
    unCtx
      (irI subUnL subUnL)
      (irLR subUnR subUnR)
  
  def subUnIrDistElimL {a b c}:
    dl.SubsetStx
      (ir (un a c) (un b c))
      (un (ir a b) c)
  :=
    (irUnDistL subId).trans
      (unCtx
        ((irUnDistR subId).trans
          (unCtx subUnL (irCtxR subUnR)))
        (irCtxL subUnR))
  
  def subUnIrDistElimR {a b c}:
    dl.SubsetStx
      (ir (un a b) (un a c))
      (un a (ir b c))
  :=
    (irUnDistL subId).trans
      (unCtx
        (irCtxL subUnL)
        ((irUnDistR subId).trans
          (unCtx (irCtxR subUnL) subUnR)))
  
  def unIr {x al ar b}
    (subA: dl.SubsetStx x (un al ar))
    (subB: dl.SubsetStx x b)
  :
    dl.SubsetStx x (un (ir al b) (ir ar b))
  :=
    trans (irI subA subB) (irUnDistL subId)
  
  
  def implIntro {x a b}
    (sub: dl.SubsetStx (ir x a) b)
  :
    dl.SubsetStx x (impl a b)
  :=
    trans
      (trans (irI subUnR em.unSymm) subUnIrDistElimR)
      (unCtxLR subId sub)
  
  def implElim {x a b}
    (subImpl: dl.SubsetStx x (impl a b))
    (subA: dl.SubsetStx x a)
  :
    dl.SubsetStx x b
  :=
    trans
      (irI subA subImpl)
      (trans (irUnDistR subId) (unCtx subPe subIrR))
  
  def implElimExact {x a}
    (subA: dl.SubsetStx x (impl x a))
  :
    dl.SubsetStx x a
  :=
    implElim subA subId
  
  def toImpl {x a b}
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx x (impl a b)
  :=
    trans
      em
      (unCtx
        (trans sub subUnR)
        subUnL)
  
  def unElimComplL {x a b}
    (ab: dl.SubsetStx x (un a b))
    (aCompl: dl.SubsetStx x (a.compl))
  :
    dl.SubsetStx x b
  :=
    trans
      (irI aCompl ab)
      (trans (irUnDistR subId) (unCtx subPe.irSymmCtx subIrR))
  
  def unElimComplR {x a b}
    (ab: dl.SubsetStx x (un a b))
    (bCompl: dl.SubsetStx x (b.compl))
  :
    dl.SubsetStx x a
  :=
    trans
      (irI bCompl ab)
      (trans (irUnDistR subId) (unCtx subIrR subPe.irSymmCtx))
  
  def unAbsorbCtxL {x a b}
    (sub: dl.SubsetStx x (un a b))
  :
    dl.SubsetStx (ir x a.compl) b
  :=
    unElimComplL (irCtxL sub) subIrR
  
  def unAbsorbCtxR {x a b}
    (sub: dl.SubsetStx x (un a b))
  :
    dl.SubsetStx (ir x b.compl) a
  :=
    unElimComplR (irCtxL sub) subIrR
  
  def unIntroCtxL {x a b}
    (sub: dl.SubsetStx (ir x a.compl) b)
  :
    dl.SubsetStx x (un a b)
  :=
    unMonoSubL (implIntro sub) subDne
  
  def unIntroCtxR {x a b}
    (sub: dl.SubsetStx (ir x b.compl) a)
  :
    dl.SubsetStx x (un a b)
  :=
    unSymm (unIntroCtxL sub)
  
  def implAddIrL {x a b c}
    (sub: dl.SubsetStx x (impl a b))
  :
    dl.SubsetStx x (impl (ir c a) (ir c b))
  :=
    implIntro
      (irI
        (irCtxR subIrCtxL)
        (irMonoCtxR subIrCtxR (implAbsorb sub)))
  
  def implAddIrR {x a b c}
    (sub: dl.SubsetStx x (impl a b))
  :
    dl.SubsetStx x (impl (ir a c) (ir b c))
  :=
    implIntro
      (irI
        (irMonoCtxR subIrCtxL (implAbsorb sub))
        (irCtxR subIrCtxR))
  
  def implCompl {x a}
    (sub: dl.SubsetStx x (impl a none))
  :
    dl.SubsetStx x (compl a)
  :=
    sub.unElim subIrR (irCtxR subNone)
  
  def complImpl {x a}
    (sub: dl.SubsetStx x (compl a))
  :
    dl.SubsetStx x (impl a none)
  :=
    unL sub
  
  def ofImpl {x a}
    (sub: dl.SubsetStx any (impl x a))
  :
    dl.SubsetStx x a
  :=
    implElimExact (trans subAny sub)
  
  
  def subContra {a b}:
    dl.SubsetStx (impl a b) (impl (compl b) (compl a))
  :=
    trans subUnSymm (unCtxLR subDni subId)
  
  def subContraElim
    {a b: SingleLaneExpr}
  :
    dl.SubsetStx (impl a.compl b.compl) (impl b a)
  :=
    em.unElimImpl
      (implIntro (unR subIrR))
      (implIntro (unL (implElim subIrL subIrR)))
  
  def contra {x a b}
    (sub: dl.SubsetStx x (impl a b))
  :
    dl.SubsetStx x (impl (compl b) (compl a))
  :=
    trans sub subContra
  
  def contraElim {x a b}
    (sub: dl.SubsetStx x (impl a.compl b.compl))
  :
    dl.SubsetStx x (impl b a)
  :=
    trans sub subContraElim
  
  def subComplUn {l r}:
    dl.SubsetStx (compl (un l r)) (ir (compl l) (compl r))
  :=
    irI (subCompl (unL subId)) (subCompl subUnR)
  
  def subComplUnElim {l r}:
    dl.SubsetStx (ir (compl l) (compl r)) (compl (un l r))
  :=
    complSwap (unCtx (complSwap subIrL) (complSwap subIrR))
  
  def complUn {x l r}
    (sub: dl.SubsetStx x (compl (un l r)))
  :
    dl.SubsetStx x (ir (compl l) (compl r))
  :=
    sub.trans subComplUn
  
  def complUnElim {x l r}
    (sub: dl.SubsetStx x (ir (compl l) (compl r)))
  :
    dl.SubsetStx x (compl (un l r))
  :=
    sub.trans subComplUnElim
  
  def complUnElimL {x l r}
    (sub: dl.SubsetStx x (compl (un l r)))
  :
    dl.SubsetStx x (compl l)
  :=
    irL (complUn sub)
  
  def complUnElimR {x l r}
    (sub: dl.SubsetStx x (compl (un l r)))
  :
    dl.SubsetStx x (compl r)
  :=
    irR (complUn sub)
  
  def byContra {x a}
    (sub: dl.SubsetStx (ir x a.compl) none)
  :
    dl.SubsetStx x a
  :=
    complElim sub (trans sub subNone)
  
  
  def fullImplElim {a b}
    (fullAb: dl.SubsetStx (full a) (full (impl a b)))
  :
    dl.SubsetStx (full a) (full b)
  :=
    implElimExact (trans fullAb (fullImplDist subId))
  
  def fullMp {x a b}
    (fullAb: dl.SubsetStx x (full (impl a b)))
    (fullA: dl.SubsetStx x (full a))
  :
    dl.SubsetStx x (full b)
  :=
    mp (fullImplDist fullAb) fullA
  
  def fullMono {x a b}
    (fa: dl.SubsetStx x (full a))
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx x (full b)
  :=
    fullMp (isFullImpl sub) fa
  
  def fullDne {x a}
    (sub: dl.SubsetStx x (full (compl (compl a))))
  :
    dl.SubsetStx x (full a)
  :=
    fullMono sub subDne
  
  def fullDni {x a}
    (sub: dl.SubsetStx x (full a))
  :
    dl.SubsetStx x (full (compl (compl a)))
  :=
    fullMono sub subDni
  
  def complFullAntimono {a b}
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx (compl (full b)) (compl (full a))
  :=
    subCompl (fullMono subId sub)
  
  def isFullAny {x}:
    dl.SubsetStx x (full any)
  :=
    fullMono (isFullImpl (subId (a := x))) subAny
  
  def isFullOfAny {x a}
    (sub: dl.SubsetStx any a)
  :
    dl.SubsetStx x (full a)
  :=
    implElim (fullImplDist (isFullImpl (x:=x) sub)) isFullAny
  
  def isFullImplElim {a b}
    (sub: dl.SubsetStx any (full (impl a b)))
  :
    dl.SubsetStx a b
  :=
    (trans (irI subAny subId) (implAbsorb (fullElim sub)))
  
  def fullUnL {x a b}
    (sub: dl.SubsetStx x (full a))
  :
    dl.SubsetStx x (full (un a b))
  :=
    fullMono sub subUnL
  
  def fullUnR {x a b}
    (sub: dl.SubsetStx x (full b))
  :
    dl.SubsetStx x (full (un a b))
  :=
    fullMono sub subUnR
  
  def subSome {a}:
    dl.SubsetStx a (some a)
  :=
    trans subDni (subCompl (fullElim subId))
  
  def someI {x a}
    (sub: dl.SubsetStx x a)
  :
    dl.SubsetStx x (some a)
  :=
    trans sub subSome
  
  def subSomeMono {a b}
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx (some a) (some b)
  :=
    complFullAntimono (subCompl sub)
  
  def someMono {x a b}
    (sa: dl.SubsetStx x (some a))
    (sub: dl.SubsetStx x (full (impl a b)))
  :
    dl.SubsetStx x (some b)
  :=
    byContra (pe
      (fullMp (irCtxL (fullMono sub subContra)) subIrR.dne)
      (irCtxL sa))
  
  def someMonoSub {x a b}
    (sa: dl.SubsetStx x (some a))
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx x (some b)
  :=
    trans sa (subSomeMono sub)
  
  def fullSome {x a}
    (sub: dl.SubsetStx x (full a))
  :
    dl.SubsetStx x (some a)
  :=
    trans sub (fullElim (fullMono subId subSome))
  
  def subSomeAddFull {a}:
    dl.SubsetStx (some a) (full (some a))
  :=
    complSwapCtx (someStripFull subId)
  
  def someAddFull {x a}
    (sub: dl.SubsetStx x (some a))
  :
    dl.SubsetStx x (full (some a))
  :=
    trans sub subSomeAddFull
  
  def fullAddSome {x a}
    (sub: dl.SubsetStx x (full a))
  :
    dl.SubsetStx x (some (full a))
  :=
    someI sub
  
  def someAddSome {x a}
    (sub: dl.SubsetStx x (some a))
  :
    dl.SubsetStx x (some (some a))
  :=
    someI sub
  
  def fullSomeIntro {x a}
    (sub: dl.SubsetStx x a)
  :
    dl.SubsetStx x (full (some a))
  :=
    someAddFull (someI sub)
  
  def fullAddFull {x a}
    (sub: dl.SubsetStx x (full a))
  :
    dl.SubsetStx x (full (full a))
  :=
    fullMono (fullSomeIntro sub) (someStripFull subId)
  
  def someStripSome {x a}
    (sub: dl.SubsetStx x (some (some a)))
  :
    dl.SubsetStx x (some a)
  :=
    sub.trans (subCompl (fullMono (fullAddFull subId) subDni))
  
  def complSomeElim {x a}
    (sub: dl.SubsetStx x (compl (some a)))
  :
    dl.SubsetStx x (compl a)
  :=
    sub.dne.fullElim
  
  def complSomeImplNone {x a}
    (sub: dl.SubsetStx x (compl (some a)))
  :
    dl.SubsetStx x (impl a none)
  :=
    trans sub.complSomeElim (complImpl subId)
  
  def someNoneElim {x a}
    (sub: dl.SubsetStx x (some none))
  :
    dl.SubsetStx x a
  :=
    noneElim (sub.trans (arbIrI (subCompl isFullAny)))
  
  
  def unfoldCtx {lane c b}
      (sub: dl.SubsetStx (const lane c) b)
    :
      dl.SubsetStx ((dl.getDef c).toLane lane) b
  :=
    trans (fold subId) sub
  
  def foldCtx {lane c b}
      (sub: dl.SubsetStx ((dl.getDef c).toLane lane) b)
    :
      dl.SubsetStx (const lane c) b
  :=
    trans (unfold subId) sub
  
  
  def subPairMono {al ar bl br}
    (sl: dl.SubsetStx al bl)
    (sr: dl.SubsetStx ar br)
  :
    dl.SubsetStx (pair al ar) (pair bl br)
  :=
    implElimExact
      (fullElim (pairMono (isFullImpl sl) (isFullImpl sr)))
  
  def pairMonoSubL {x a c b}
    (sub: dl.SubsetStx x (pair a b))
    (ac: dl.SubsetStx a c)
  :
    dl.SubsetStx x (pair c b)
  :=
    sub.trans (subPairMono ac subId)
  
  def pairMonoSubR {x a b c}
    (sub: dl.SubsetStx x (pair a b))
    (bc: dl.SubsetStx b c)
  :
    dl.SubsetStx x (pair a c)
  :=
    sub.trans (subPairMono subId bc)
  
  def pairMonoCtxSubL {x a c b}
    (sub: dl.SubsetStx (pair a b) x)
    (ca: dl.SubsetStx c a)
  :
    dl.SubsetStx (pair c b) x
  :=
    (subPairMono ca subId).trans sub
  
  def pairMonoCtxSubR {x a b c}
    (sub: dl.SubsetStx (pair a b) x)
    (cb: dl.SubsetStx c b)
  :
    dl.SubsetStx (pair a c) x
  :=
    (subPairMono subId cb).trans sub
  
  def nullPairComplPair {x a b}:
    dl.SubsetStx
      x
      (finUn [
        null,
        pair (compl a) any,
        pair any (compl b),
        pair a b
      ])
  :=
    unElimSub
      em
      (unR (unR subUnR))
      (trans
        (complPairElim subId)
        (unCtxLR subId (unCtxLR subId subUnL)))
  
  def pairNoneElimL {x a b}
    (sub: dl.SubsetStx x (pair none a))
  :
    dl.SubsetStx x b
  :=
    let subPair := sub.trans (subPairMono subAny subAny)
    pe sub (complPair (unR (unL subPair)))
  
  def pairNoneElimR {x a b}
    (sub: dl.SubsetStx x (pair a none))
  :
    dl.SubsetStx x b
  :=
    let subPair := sub.trans (subPairMono subAny subAny)
    pe sub (complPair (unR (unR subPair)))
  
  def nullPair {x}:
    dl.SubsetStx x (un null (pair any any))
  :=
    (nullPairComplPair (a := none)).unElim
      (irCtxR subUnL)
      (unElimCont
        (irCtxR ((pairMonoSubL subId subAny).unR))
        (unElimCont
          (irCtxR ((pairMonoSubR subId subAny).unR))
          (irCtxR (pairNoneElimR subId))))
  
  def subSimplePairInduction {a p}
    (sub: dl.SubsetStx (un null (pair p p)) p)
  :
    dl.SubsetStx a p
  :=
    implElimExact (fullElim (simplePairInduction (isFullImpl sub)))
  
  def pairIrOfIr {x al ar bl br}
    (sub: dl.SubsetStx x (ir (pair al ar) (pair bl br)))
  :
    dl.SubsetStx x (pair (ir al bl) (ir ar br))
  :=
    pairIr (irL sub) (irR sub)
  
  def pairIrL {x a b c}
    (subA: dl.SubsetStx x (pair a c))
    (subB: dl.SubsetStx x (pair b c))
  :
    dl.SubsetStx x (pair (ir a b) c)
  :=
    pairMonoSubR (pairIr subA subB) subIrL
  
  def pairIrR {x a b c}
    (subA: dl.SubsetStx x (pair a b))
    (subB: dl.SubsetStx x (pair a c))
  :
    dl.SubsetStx x (pair a (ir b c))
  :=
    pairMonoSubL (pairIr subA subB) subIrL
  
  def irPairL {x a b c}
    (sub: dl.SubsetStx x (pair (ir a b) c))
  :
    dl.SubsetStx x (ir (pair a c) (pair b c))
  :=
    sub.trans
      (irI (subPairMono subIrL subId)
      (subPairMono subIrR subId))
  
  def irPairR {x a b c}
    (sub: dl.SubsetStx x (pair a (ir b c)))
  :
    dl.SubsetStx x (ir (pair a b) (pair a c))
  :=
    sub.trans
      (irI
        (subPairMono subId subIrL)
        (subPairMono subId subIrR))
  
  def irPair {x al ar bl br}
    (sub: dl.SubsetStx x (pair (ir al ar) (ir bl br)))
  :
    dl.SubsetStx x (ir (pair al bl) (pair ar br))
  :=
    irI
      (sub.trans (subPairMono subIrL subIrL))
      (sub.trans (subPairMono subIrR subIrR))
  
  def pairComplUnL {x a b c}
    (subA: dl.SubsetStx x (pair (compl a) c))
    (subB: dl.SubsetStx x (pair (compl b) c))
  :
    dl.SubsetStx x (pair (compl (un a b)) c)
  :=
    pairMonoSubL (pairIrL subA subB) subComplUnElim
  
  def pairComplUnR {x a b c}
    (subA: dl.SubsetStx x (pair a (compl b)))
    (subB: dl.SubsetStx x (pair a (compl c)))
  :
    dl.SubsetStx x (pair a (compl (un b c)))
  :=
    pairMonoSubR (pairIrR subA subB) subComplUnElim
  
  def unPairL {x a b c}
    (sub: dl.SubsetStx x (pair (un a b) c))
  :
    dl.SubsetStx x (un (pair a c) (pair b c))
  :=
    sub.trans <|
    subComplElim <|
    subComplUn.trans <|
    (irLR (complPairElim subId) (complPairElim subId)).trans <|
    (irLR subUnSymm subUnSymm).trans <|
    subUnIrDistElimL.trans <|
    (unCtxLR
      (subUnIrDistElimL.trans
        (unCtxLR (pairComplUnL subIrL subIrR) subId))
      subId).trans <|
    subUnSymm.trans <|
    complPair subId
  
  def unPairR {x a b c}
    (sub: dl.SubsetStx x (pair a (un b c)))
  :
    dl.SubsetStx x (un (pair a b) (pair a c))
  :=
    sub.trans <|
    subComplElim <|
    subComplUn.trans <|
    (irLR (complPairElim subId) (complPairElim subId)).trans <|
    (irLR subUnSymm subUnSymm).trans <|
    subUnIrDistElimL.trans <|
    (unCtxLR
      (subUnIrDistElimR.trans
        (unCtxLR subId (pairComplUnR subIrL subIrR)))
      subId).trans <|
    subUnSymm.trans <|
    complPair subId
  
  def pairFullL {x a b f}
    (subF: dl.SubsetStx x (full f))
    (subP: dl.SubsetStx x (pair a b))
  :
    dl.SubsetStx x (pair (full f) b)
  :=
    sorry
  
  def pairFullR {x a b f}
    (subF: dl.SubsetStx x (full f))
    (subP: dl.SubsetStx x (pair a b))
  :
    dl.SubsetStx x (pair a (full f))
  :=
    sorry
  
  def pairFullElimFullL {x a b}
    (sub: dl.SubsetStx x (pair (full a) b))
  :
    dl.SubsetStx x (full a)
  :=
    sorry
  
  def pairFullElimPairL {x a b}
    (sub: dl.SubsetStx x (pair (full a) b))
  :
    dl.SubsetStx x (pair any b)
  :=
    sorry
  
  def pairFullElimFullR {x a b}
    (sub: dl.SubsetStx x (pair a (full b)))
  :
    dl.SubsetStx x (full b)
  :=
    sorry
  
  def pairFullElimPairR {x a b}
    (sub: dl.SubsetStx x (pair a (full b)))
  :
    dl.SubsetStx x (pair a any)
  :=
    sorry
  
  def pairSomeL {x a b s}
    (subS: dl.SubsetStx x (some s))
    (subP: dl.SubsetStx x (pair a b))
  :
    dl.SubsetStx x (pair (some s) b)
  :=
    sorry
  
  def pairSomeR {x a b s}
    (subS: dl.SubsetStx x (some s))
    (subP: dl.SubsetStx x (pair a b))
  :
    dl.SubsetStx x (pair a (some s))
  :=
    sorry
  
  def pairSomeElimSomeL {x a b}
    (sub: dl.SubsetStx x (pair (some a) b))
  :
    dl.SubsetStx x (some a)
  :=
    sorry
  
  def pairSomeElimPairL {x a b}
    (sub: dl.SubsetStx x (pair (some a) b))
  :
    dl.SubsetStx x (pair any b)
  :=
    sorry
  
  def pairSomeElimSomeR {x a b}
    (sub: dl.SubsetStx x (pair a (some b)))
  :
    dl.SubsetStx x (some b)
  :=
    sorry
  
  def pairSomeElimPairR {x a b}
    (sub: dl.SubsetStx x (pair a (some b)))
  :
    dl.SubsetStx x (pair a any)
  :=
    sorry
  
  def pairUnL {x a b c}
    (sub: dl.SubsetStx x (un (pair a c) (pair b c)))
  :
    dl.SubsetStx x (pair (un a b) c)
  :=
    sub.trans
      (unCtx
        (subPairMono subUnL subId)
        (subPairMono subUnR subId))
  
  def pairUnR {x a b c}
    (sub: dl.SubsetStx x (un (pair a b) (pair a c)))
  :
    dl.SubsetStx x (pair a (un b c))
  :=
    sub.trans
      (unCtx
        (subPairMono subId subUnL)
        (subPairMono subId subUnR))
  
  def irNullPairElim {x a b}
    (sub: dl.SubsetStx x (ir null (pair a b)))
  :
    dl.SubsetStx x b
  :=
    pe (irR sub) (complPair (unL (irL sub)))
  
  def pairUnfoldL {x lane c b}
    (sub: dl.SubsetStx x (pair (const lane c) b))
  :
    dl.SubsetStx x (pair ((dl.getDef c).toLane lane) b)
  :=
    pairMonoSubL sub (unfold subId)
  
  def pairUnfoldR {x lane c a}
    (sub: dl.SubsetStx x (pair a (const lane c)))
  :
    dl.SubsetStx x (pair a ((dl.getDef c).toLane lane))
  :=
    pairMonoSubR sub (unfold subId)
  
  def pairFoldL {x lane c b}
    (sub: dl.SubsetStx x (pair ((dl.getDef c).toLane lane) b))
  :
    dl.SubsetStx x (pair (const lane c) b)
  :=
    pairMonoSubL sub (fold subId)
  
  def pairFoldR {x lane c a}
    (sub: dl.SubsetStx x (pair a ((dl.getDef c).toLane lane)))
  :
    dl.SubsetStx x (pair a (const lane c))
  :=
    pairMonoSubR sub (fold subId)
  
  def someNull {x}:
    dl.SubsetStx x (some null)
  :=
    someMonoSub (nullFullSome (isFullImpl subId)) (irL subId)
  
  def somePairElimL {x a b}
    (sub: dl.SubsetStx x (some (pair a b)))
  :
    dl.SubsetStx x (some a)
  :=
    byContra
      (someNoneElim
        (someMonoSub
          (someMono
            (irCtxL sub)
            (pairMono
              (fullMono (dne subIrR) subUnL)
              (isFullImpl subId)))
          (pairNoneElimL subId)))
  
  def somePairElimR {x a b}
    (sub: dl.SubsetStx x (some (pair a b)))
  :
    dl.SubsetStx x (some b)
  :=
    byContra
      (someNoneElim
        (someMonoSub
          (someMono
            (irCtxL sub)
            (pairMono
              (isFullImpl subId)
              (fullMono (dne subIrR) subUnL)))
          (pairNoneElimR subId)))
  
  def pairMonoZth {x al bl ar br}
    (sub: dl.SubsetStx x (full (impl (pair al ar) (pair bl br))))
    (subSome: dl.SubsetStx x (some ar))
  :
    dl.SubsetStx x (full (impl al bl))
  :=
    sorry
  
  def pairMonoFst {x al bl ar br}
    (sub: dl.SubsetStx x (full (impl (pair al ar) (pair bl br))))
    (subSome: dl.SubsetStx x (some ar))
  :
    dl.SubsetStx x (full (impl ar br))
  :=
    sorry
  
  
  def someVar {x i}:
    dl.SubsetStx x (some (var i))
  :=
    someMonoSub (varFullSome (isFullImpl subId)) (irL subId)
  
  def varSubsingleton {x i}:
    dl.SubsetStx x (var i).isSubsingleton
  :=
    arbIrI (implIntro (varSomeFull (irR subId)))
  
  def replaceVar {x i a}
    (subVar: dl.SubsetStx x (var i))
    (subSome: dl.SubsetStx x (some (ir (var i) a)))
  :
    dl.SubsetStx x a
  :=
    mp subSome.varSomeFull.fullElim subVar
  
  
  def nullSubsingleton {x}:
    dl.SubsetStx x null.isSubsingleton
  :=
    arbIrI (implIntro (nullSomeFull subIrR))
  
  def arbIrElimVar {x a}
    (i: Nat)
    (sub: dl.SubsetStx x (arbIr a))
  :
    dl.SubsetStx x (a.instantiateVar (var i))
  :=
    arbIrElim sub someVar varSubsingleton
  
  def arbIrPop {x a}
    (sub: dl.SubsetStx x (arbIr a))
  :
    dl.SubsetStx x.lift a
  :=
    lift_d0_instantiateVar_eq a ▸ arbIrElimVar 0 sub.toLift
  
  def arbIrUnLiftDistL {x a b}
    (sub: dl.SubsetStx x (arbIr (un a.lift b)))
  :
    dl.SubsetStx x (un a (arbIr b))
  :=
    unIntroCtxL (arbIrI (unAbsorbCtxL (arbIrPop sub)))
  
  def arbIrUnLiftDistR {x a b}
    (sub: dl.SubsetStx x (arbIr (un a b.lift)))
  :
    dl.SubsetStx x (un (arbIr a) b)
  :=
    unIntroCtxR (arbIrI (unAbsorbCtxR (arbIrPop sub)))
  
  def arbIrMono {x a b}
    (sub: dl.SubsetStx x (arbIr a))
    (impl: dl.SubsetStx x.lift (impl a b))
  :
    dl.SubsetStx x (arbIr b)
  :=
    arbIrI (mp impl (arbIrPop sub))
  
  def arbIrMonoSub {x a b}
    (sub: dl.SubsetStx x (arbIr a))
    (impl: dl.SubsetStx a b)
  :
    dl.SubsetStx x (arbIr b)
  :=
    arbIrMono sub impl.toImpl
  
  def subArbIrMono {a b}
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx (arbIr a) (arbIr b)
  :=
    arbIrMonoSub subId sub
  
  def pointwise {x a}
    (sub: dl.SubsetStx (ir (var 0) x.lift) (ir (var 0) a.lift))
  :
    dl.SubsetStx x a
  :=
    let subImpl: dl.SubsetStx x.lift (impl (var 0) a.lift) :=
      implIntro (irR (irSymmCtx sub))
    let subUnNone: dl.SubsetStx x (un none a) :=
      arbIrUnLiftDistR (arbIrI subImpl)
    unElimSub subUnNone (noneElim subId) subId
  
  def pointwiseCtx {x a}
    (sub: dl.SubsetStx (ir (var 0) x.lift) a.lift)
  :
    dl.SubsetStx x a
  :=
    pointwise (irI subIrCtxL sub)
  
  
  def arbUnCtxI {a b}
    (sub: dl.SubsetStx a b.lift)
  :
    dl.SubsetStx (arbUn a) b
  :=
    complSwapCtx (arbIrI (subCompl sub))
  
  def arbUnPopCtx {x a}
    (sub: dl.SubsetStx (arbUn a) x)
  :
    dl.SubsetStx a x.lift
  :=
    subComplElim (arbIrPop (dne (subCompl sub)))
  
  def arbUnI {x a t}
    (isSome: dl.SubsetStx x (some t))
    (isSubsingle: dl.SubsetStx x t.isSubsingleton)
    (sub: dl.SubsetStx x (a.instantiateVar t))
  :
    dl.SubsetStx x (arbUn a)
  :=
    let y := ir x (arbIr (compl a))
    let aInst := a.instantiateVar t
    
    let subYa: dl.SubsetStx y aInst :=
      trans subIrL sub
    let subYnotA: dl.SubsetStx y (compl aInst) :=
      subIrR.arbIrElim
        (trans subIrL isSome)
        (irCtxL isSubsingle)
    
    let subYNope: dl.SubsetStx y (ir aInst (compl aInst)) :=
      irI subYa subYnotA
    
    trans (implIntro subYNope) (unCtx subId subPe)
  
  def arbUnVarI {x a i}
    (sub: dl.SubsetStx x (a.instantiateVar (var i)))
  :
    dl.SubsetStx x (arbUn a)
  :=
    arbUnI someVar varSubsingleton sub
  
  def arbUnElimImpl {x a b}
    (sub: dl.SubsetStx x (arbUn a))
    (impl: dl.SubsetStx x.lift (impl a b.lift))
  :
    dl.SubsetStx x b
  :=
    let subYComplA :=
      trans
        (irUnDistL (irLR impl subId))
        (unCtx subIrL subPe)
    
    complElim (arbIrI subYComplA) (trans subIrL sub)
  
  def arbUnElim {x a b}
    (sub: dl.SubsetStx x (arbUn a))
    (impl: dl.SubsetStx (ir x.lift a) b.lift)
  :
    dl.SubsetStx x b
  :=
    arbUnElimImpl sub (implIntro impl)
  
  def arbUnMono {x a b}
    (sub: dl.SubsetStx x (arbUn a))
    (subImpl: dl.SubsetStx x.lift (impl a b))
  :
    dl.SubsetStx x (arbUn b)
  :=
    let y := ir x (arbIr (compl b))
    let subYArbUna: dl.SubsetStx y (arbUn a) := subIrL.trans sub
    let subYComplB: dl.SubsetStx y.lift (compl b) := arbIrPop subIrR
    let subYImplANone: dl.SubsetStx y.lift (impl a none) :=
      (unElimComplR (subIrL.toLift.trans subImpl) subYComplB).unL
    let subYNone: dl.SubsetStx y none :=
      arbUnElimImpl subYArbUna subYImplANone
    complI subIrR (noneElim subYNone)
  
  def arbUnMonoSub {x a b}
    (sub: dl.SubsetStx x (arbUn a))
    (impl: dl.SubsetStx a b)
  :
    dl.SubsetStx x (arbUn b)
  :=
    arbUnMono sub impl.toImpl
  
  def subArbUnMono {a b}
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx (arbUn a) (arbUn b)
  :=
    arbUnMonoSub subId sub
  
  
  def complArbIrElim {x a}
    (sub: dl.SubsetStx x (compl (arbIr a)))
  :
    dl.SubsetStx x (arbUn (compl a))
  :=
    trans sub <|
    subCompl <|
    arbIrI (trans (arbIrPop subId) subDne)
  
  def complArbUnElim {x a}
    (sub: dl.SubsetStx x (compl (arbUn a)))
  :
    dl.SubsetStx x (arbIr (compl a))
  :=
    dne sub
  
  def complArbIrComplElim {x a}
    (sub: dl.SubsetStx x (compl (arbIr (compl a))))
  :
    dl.SubsetStx x (arbUn a)
  :=
    sub
  
  def complArbUnComplElim {x a}
    (sub: dl.SubsetStx x (compl (arbUn (compl a))))
  :
    dl.SubsetStx x (arbIr a)
  :=
    arbIrI (trans (arbIrPop (dne sub)) subDne)
  
  
  def pairZthFst {x e}
    (subE: dl.SubsetStx x e)
    (subPair: dl.SubsetStx x (pair any any))
  :
    dl.SubsetStx x (pair (zth e.lift) (fst e.lift))
  :=
    sorry
  
  def nullPairZthFst {x e}
    (subE: dl.SubsetStx x e)
  :
    dl.SubsetStx x (un null (pair (zth e.lift) (fst e.lift)))
  :=
    sorry
  
  def zthPair {x a b}
    (subB: dl.SubsetStx x (some b))
    (sub: dl.SubsetStx x a)
  :
    dl.SubsetStx x (zth (pair a.lift b.lift))
  :=
    sorry
  
  def zthPairElim {x a b}
    (sub: dl.SubsetStx x (zth (pair a.lift (lift b))))
  :
    dl.SubsetStx x a
  :=
    sub.arbUnElim
      (irCtxR
        (replaceVar
          subIrR
          (irCtxL
            (trans
              (someMonoSub subId (pairIrOfIr subId))
              (somePairElimL subId)))))
  
  def fstPair {x a b}
    (subA: dl.SubsetStx x (some a))
    (sub: dl.SubsetStx x b)
  :
    dl.SubsetStx x (fst (pair a.lift b.lift))
  :=
    sorry
  
  def fstPairElim {x a b}
    (sub: dl.SubsetStx x (fst (pair (lift a) b.lift)))
  :
    dl.SubsetStx x b
  :=
    sub.arbUnElim
      (irCtxR
        (replaceVar
          subIrR
          (irCtxL
            (trans
              (someMonoSub subId (pairIrOfIr subId))
              (somePairElimR subId)))))
  
  def zthMono {x a}
    (sub: dl.SubsetStx x a)
  :
    dl.SubsetStx (zth x.lift) (zth a.lift)
  :=
    subArbUnMono
      (irLR (subSomeMono ((irLR subId (toLift sub)))) subId)
  
  def projZth {x a b}
    (sub: dl.SubsetStx x (pair a b))
  :
    dl.SubsetStx (zth x.lift) a
  :=
    trans (zthMono sub) (zthPairElim subId)
  
  def fstMono {x a}
    (sub: dl.SubsetStx x a)
  :
    dl.SubsetStx (fst x.lift) (fst a.lift)
  :=
    subArbUnMono
      (irLR (subSomeMono ((irLR subId (toLift sub)))) subId)
  
  def projFst {x a b}
    (sub: dl.SubsetStx x (pair a b))
  :
    dl.SubsetStx (fst x.lift) b
  :=
    trans (fstMono sub) sorry
  
  
  def pairArbIrL {x a b}
    (sub: dl.SubsetStx x (arbIr (pair a b.lift)))
  :
    dl.SubsetStx x (pair (arbIr a) b)
  :=
    sorry
  
  def pairArbIrR {x a b}
    (sub: dl.SubsetStx x (arbIr (pair a.lift b)))
  :
    dl.SubsetStx x (pair a (arbIr b))
  :=
    sorry
  
  def arbIrPairL {x a b}
    (sub: dl.SubsetStx x (pair (arbIr a) b))
  :
    dl.SubsetStx x (arbIr (pair a b.lift))
  :=
    arbIrI (sub.toLift.trans (subPairMono (arbIrPop subId) subId))
  
  def arbIrPairR {x a b}
    (sub: dl.SubsetStx x (pair a (arbIr b)))
  :
    dl.SubsetStx x (arbIr (pair a.lift b))
  :=
    arbIrI (sub.toLift.trans (subPairMono subId (arbIrPop subId)))
  
  def arbUnPairL {x a b}
    (sub: dl.SubsetStx x (pair (arbUn a) b))
  :
    dl.SubsetStx x (arbUn (pair a b.lift))
  :=
    sorry
  
  def arbUnPairR {x a b}
    (sub: dl.SubsetStx x (pair a (arbUn b)))
  :
    dl.SubsetStx x (arbUn (pair a.lift b))
  :=
    sorry
  
  def pairArbUnL {x a b}
    (sub: dl.SubsetStx x (arbUn (pair a b.lift)))
  :
    dl.SubsetStx x (pair (arbUn a) b)
  :=
    sorry
  
  def pairArbUnR {x a b}
    (sub: dl.SubsetStx x (arbUn (pair a.lift b)))
  :
    dl.SubsetStx x (pair a (arbUn b))
  :=
    sorry
  
end DefList.SubsetStx
