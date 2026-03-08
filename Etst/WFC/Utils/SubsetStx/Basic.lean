import Etst.WFC.Ch5_SubsethoodPS
import Etst.WFC.Utils.SubsetStx.MapFv

namespace Etst
open Expr


namespace DefList.SubsetStx
  variable {dl: DefList}
  
  /-
    Note: It is an anti-pattern to use `trans` too much, especially
    if the calls are chained, because it prevents efficient sharing
    of context between the steps. For this reason, it is good to
    write lemmas as transforming `x ⊆ a` into `x ⊆ b` (function form)
    rather than proving `a ⊆ b` (sub form). Unlike using `trans`
    extensively, this function form composes well.
    
    The few existing sub form lemmas that are here are just to save
    characters because they are very common as proof leafs. (Plus
    subCompl & friends, which have no function form analogues.)
  -/
  
  def liftInst {x a t}
    (sub: dl.SubsetStx x a)
  :
    dl.SubsetStx x (a.lift.instantiateVar t)
  :=
    (lift_instantiateVar_eq a t).symm ▸ sub
  
  
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
  
  def irLR {al ar bl br}
    (subL: dl.SubsetStx al bl)
    (subR: dl.SubsetStx ar br)
  :
    dl.SubsetStx (ir al ar) (ir bl br)
  :=
    irI subL.irCtxL subR.irCtxR
  
  def irSymm {x l r}
    (sub: dl.SubsetStx x (ir l r))
  :
    dl.SubsetStx x (ir r l)
  :=
    irI (irR sub) (irL sub)
  
  def irMonoCtxL {a al ar b}
    (sub: dl.SubsetStx (ir al ar) b)
    (subA: dl.SubsetStx a al)
  :
    dl.SubsetStx (ir a ar) b
  :=
    trans (irLR subA subId) sub
  
  def irMonoCtxR {a al ar b}
    (sub: dl.SubsetStx (ir al ar) b)
    (subA: dl.SubsetStx a ar)
  :
    dl.SubsetStx (ir al a) b
  :=
    trans (irLR subId subA) sub
  
  def irMonoCtx {l0 l1 r0 r1 a}
    (sub: dl.SubsetStx (ir l1 r1) a)
    (subL: dl.SubsetStx l0 l1)
    (subR: dl.SubsetStx r0 r1)
  :
    dl.SubsetStx (ir l0 r0) a
  :=
    trans (irLR subL subR) sub
  
  def mpIr {x a b}
    (sub: dl.SubsetStx x a)
    (subAb: dl.SubsetStx (ir x a) b)
  :
    dl.SubsetStx x b
  :=
    trans (irI subId sub) subAb
  
  
  def pe {x a b}
    (sub: dl.SubsetStx x b)
    (subC: dl.SubsetStx x b.compl)
  :
    dl.SubsetStx x a
  :=
    complElim (irCtxL sub) (irCtxL subC)
  
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
  
  def mpIrCompl {x a b}
    (sub: dl.SubsetStx x a.compl)
    (subBa: dl.SubsetStx (ir x b) a)
  :
    dl.SubsetStx x (compl b)
  :=
    complI subBa (irCtxL sub)
  
  def mpIrContra {x a b}
    (h: dl.SubsetStx x a)
    (sub: dl.SubsetStx (ir x (compl b)) (compl a))
  :
    dl.SubsetStx x b
  :=
    dne (mpIrCompl (dni h) sub)
  
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
    trans (dni subId) (trans (subCompl sub) (dne subId))
  
  def complSwapCtx {a b}
    (sub: dl.SubsetStx (compl a) b)
  :
    dl.SubsetStx (compl b) a
  :=
    dne (mpIrCompl subId (irCtxR sub))
  
  def complSwap {a b}
    (sub: dl.SubsetStx a (compl b))
  :
    dl.SubsetStx b (compl a)
  :=
    mpIrCompl (dni subId) (irCtxR sub)
  
  
  def anyI {x}:
    dl.SubsetStx x any
  :=
    complI (b := null) (noneElim subIrR) (noneElim subIrR)
  
  
  def mp {x a b}
    (subAb: dl.SubsetStx x (impl a b))
    (subA: dl.SubsetStx x a)
  :
    dl.SubsetStx x b
  :=
    complElim (irCtxL subAb) (dni (irI (dni (irCtxL subA)) subIrR))
  
  def implAbsorb {x a b}
    (sub: dl.SubsetStx x (impl a b))
  :
    dl.SubsetStx (ir x a) b
  :=
    mp (irCtxL sub) subIrR
  
  
  def unL {x a b}
    (sub: dl.SubsetStx x a)
  :
    dl.SubsetStx x (un a b)
  :=
    complI (irCtxL sub) (irCtxR subIrL)
  
  def unR {x a b}
    (sub: dl.SubsetStx x b)
  :
    dl.SubsetStx x (un a b)
  :=
    complI (irCtxL sub) (irCtxR subIrR)
  
  def subUnL {a b}:
    dl.SubsetStx a (un a b)
  :=
    unL subId
  
  def subUnR {a b}:
    dl.SubsetStx b (un a b)
  :=
    unR subId
  
  def unElim {x l r a}
    (sub: dl.SubsetStx x (un l r))
    (subL: dl.SubsetStx (ir x l) a)
    (subR: dl.SubsetStx (ir x r) a)
  :
    dl.SubsetStx x a
  :=
    complElim
      (irI
        (mpIrCompl subIrR (irMonoCtx subL subIrL subId))
        (mpIrCompl subIrR (irMonoCtx subR subIrL subId)))
      (irCtxL sub)
  
  def unElimSub {x l r a}
    (sub: dl.SubsetStx x (un l r))
    (subL: dl.SubsetStx l a)
    (subR: dl.SubsetStx r a)
  :
    dl.SubsetStx x a
  :=
    unElim sub (irCtxR subL) (irCtxR subR)
  
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
  
  def em {x a}:
    dl.SubsetStx x (un a a.compl)
  :=
    complI (irCtxR subIrL) (irCtxR subIrR)
  
  def unSymm {x l r}
    (sub: dl.SubsetStx x (un l r))
  :
    dl.SubsetStx x (un r l)
  :=
    complI (irCtxR (irSymm subId)) (irCtxL sub)
  
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
    subIrR.unElim
      (irMonoCtxL subL subIrL)
      (irMonoCtxL subR subIrL)
  
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
          (irMonoCtxL (implAbsorb subL) subIrL)
          (irCtxL subIrR))
        (complI
          (irMonoCtxL (implAbsorb subR) subIrL)
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
  
  def irUnDistElimL {x a b c}
    (sub: dl.SubsetStx x (un (ir a c) (ir b c)))
  :
    dl.SubsetStx x (ir (un a b) c)
  :=
    sub.unElimSub
      (irI (irCtxL subUnL) subIrR)
      (irI (irCtxL subUnR) subIrR)
  
  def irUnDistElimR {x a b c}
    (sub: dl.SubsetStx x (un (ir a b) (ir a c)))
  :
    dl.SubsetStx x (ir a (un b c))
  :=
    sub.unElimSub
      (irI subIrL (irCtxR subUnL))
      (irI subIrL (irCtxR subUnR))
  
  def unIrDistL {x a b c}
    (sub: dl.SubsetStx x (un (ir a b) c))
  :
    dl.SubsetStx x (ir (un a c) (un b c))
  :=
    unElimSub sub (irLR subUnL subUnL) (irI subUnR subUnR)
  
  def unIrDistR {x a b c}
    (sub: dl.SubsetStx x (un a (ir b c)))
  :
    dl.SubsetStx x (ir (un a b) (un a c))
  :=
    unElimSub sub (irI subUnL subUnL) (irLR subUnR subUnR)
  
  def unIrDistElimL {x a b c}
    (sub: dl.SubsetStx x (ir (un a c) (un b c)))
  :
    dl.SubsetStx x (un (ir a b) c)
  :=
    (irUnDistL sub).unElimSub
      (unMonoSubR (irUnDistR subId) subIrR)
      (irCtxL subUnR)
  
  def unIrDistElimR {x a b c}
    (sub: dl.SubsetStx x (ir (un a b) (un a c)))
  :
    dl.SubsetStx x (un a (ir b c))
  :=
    (irUnDistL sub).unElimSub
      (irCtxL subUnL)
      (unMonoSubL (irUnDistR subId) subIrR)
  
  def unIr {x al ar b}
    (subA: dl.SubsetStx x (un al ar))
    (subB: dl.SubsetStx x b)
  :
    dl.SubsetStx x (un (ir al b) (ir ar b))
  :=
    irUnDistL (irI subA subB)
  
  
  def implIntro {x a b}
    (sub: dl.SubsetStx (ir x a) b)
  :
    dl.SubsetStx x (impl a b)
  :=
    unMonoSubR (unIrDistElimR (irI subUnR em.unSymm)) sub
  
  def toImpl {x a b}
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx x (impl a b)
  :=
    unElimSub em (unR sub) subUnL
  
  def unElimComplL {x a b}
    (ab: dl.SubsetStx x (un a b))
    (aCompl: dl.SubsetStx x (a.compl))
  :
    dl.SubsetStx x b
  :=
    unElimSub
      (irUnDistR (irI aCompl ab))
      (pe subIrR subIrL)
      subIrR
  
  def unElimComplR {x a b}
    (ab: dl.SubsetStx x (un a b))
    (bCompl: dl.SubsetStx x (b.compl))
  :
    dl.SubsetStx x a
  :=
    unElimSub
      (irUnDistR (irI bCompl ab))
      subIrR
      (pe subIrR subIrL)
  
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
    unMonoSubL (implIntro sub) (dne subId)
  
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
        (irCtxR subIrL)
        (irMonoCtxR (implAbsorb sub) subIrR))
  
  def implAddIrR {x a b c}
    (sub: dl.SubsetStx x (impl a b))
  :
    dl.SubsetStx x (impl (ir a c) (ir b c))
  :=
    implIntro
      (irI
        (irMonoCtxR (implAbsorb sub) subIrL)
        (irCtxR subIrR))
  
  def implAddUnL {x a b c}
    (sub: dl.SubsetStx x (impl a b))
  :
    dl.SubsetStx x (impl (un c a) (un c b))
  :=
    implIntro
      (subIrR.unElim
        (unL subIrR)
        (unR (mp (irCtxL (irCtxL sub)) subIrR)))
  
  def implAddUnR {x a b c}
    (sub: dl.SubsetStx x (impl a b))
  :
    dl.SubsetStx x (impl (un a c) (un b c))
  :=
    implIntro
      (subIrR.unElim
        (unL (mp (irCtxL (irCtxL sub)) subIrR))
        (unR subIrR))
  
  def curry {x a b c}
    (sub: dl.SubsetStx x (impl (ir a b) c))
  :
    dl.SubsetStx x (impl a (impl b c))
  :=
    implIntro
      (implIntro
        (mp
          (irCtxL (irCtxL sub))
          (irI (irCtxL subIrR) subIrR)))
  
  def uncurry {x a b c}
    (sub: dl.SubsetStx x (impl a (impl b c)))
  :
    dl.SubsetStx x (impl (ir a b) c)
  :=
    implIntro
      (mp
        (mp (irCtxL sub) (irCtxR subIrL))
        (irCtxR subIrR))
  
  def implCompl {x a}
    (sub: dl.SubsetStx x (impl a none))
  :
    dl.SubsetStx x (compl a)
  :=
    sub.unElim subIrR (noneElim subIrR)
  
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
    mp (trans anyI sub) subId
  
  def implUnOfL {x a b c}
    (sub: dl.SubsetStx x (impl a b))
  :
    dl.SubsetStx x (impl a (un b c))
  :=
    implIntro (unL (implAbsorb sub))
  
  def implUnOfR {x a b c}
    (sub: dl.SubsetStx x (impl a c))
  :
    dl.SubsetStx x (impl a (un b c))
  :=
    implIntro (unR (implAbsorb sub))
  
  def implTrans {x a b c}
    (ab: dl.SubsetStx x (impl a b))
    (bc: dl.SubsetStx x (impl b c))
  :
    dl.SubsetStx x (impl a c)
  :=
    implIntro (mp (irCtxL bc) (implAbsorb ab))
  
  def implTransSub {x a b c}
    (ab: dl.SubsetStx x (impl a b))
    (bc: dl.SubsetStx b c)
  :
    dl.SubsetStx x (impl a c)
  :=
    implIntro (mp (toImpl bc) (implAbsorb ab))
  
  def subTransImpl {x a b c}
    (ab: dl.SubsetStx a b)
    (bc: dl.SubsetStx x (impl b c))
  :
    dl.SubsetStx x (impl a c)
  :=
    implIntro (mp (irCtxL bc) (irCtxR ab))
  
  
  def contra {x a b}
    (sub: dl.SubsetStx x (impl a b))
  :
    dl.SubsetStx x (impl (compl b) (compl a))
  :=
    implIntro
      (mpIrCompl subIrR (irMonoCtxL (implAbsorb sub) subIrL))
  
  def contraElim {x a b}
    (sub: dl.SubsetStx x (impl a.compl b.compl))
  :
    dl.SubsetStx x (impl b a)
  :=
    implIntro
      (mpIrContra subIrR (irMonoCtxL (implAbsorb sub) subIrL))
  
  def complUn {x l r}
    (sub: dl.SubsetStx x (compl (un l r)))
  :
    dl.SubsetStx x (ir (compl l) (compl r))
  :=
    dne sub
  
  def complUnElim {x l r}
    (sub: dl.SubsetStx x (ir (compl l) (compl r)))
  :
    dl.SubsetStx x (compl (un l r))
  :=
    dni sub
  
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
    complElim sub (noneElim sub)
  
  
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
  
  def fullSubTransImpl {x a b c}
    (ab: dl.SubsetStx a b)
    (bc: dl.SubsetStx x (full (impl b c)))
  :
    dl.SubsetStx x (full (impl a c))
  :=
    fullMono bc (implIntro (mp subIrL (irCtxR ab)))
  
  def fullImplTransSub {x a b c}
    (ab: dl.SubsetStx x (full (impl a b)))
    (bc: dl.SubsetStx b c)
  :
    dl.SubsetStx x (full (impl a c))
  :=
    fullMono ab (implIntro (trans (implAbsorb subId) bc))
  
  def fullIr {x a b}
    (subA: dl.SubsetStx x (full a))
    (subB: dl.SubsetStx x (full b))
  :
    dl.SubsetStx x (full (ir a b))
  :=
    fullMp (fullMono subB (implIntro (irSymm subId))) subA
  
  def fullImplIr {x a b c}
    (subAb: dl.SubsetStx x (full (impl a b)))
    (subBc: dl.SubsetStx x (full (impl a c)))
  :
    dl.SubsetStx x (full (impl a (ir b c)))
  :=
    fullMono (fullIr subAb subBc) (unIrDistElimR subId)
  
  def fullDne {x a}
    (sub: dl.SubsetStx x (full (compl (compl a))))
  :
    dl.SubsetStx x (full a)
  :=
    fullMono sub (dne subId)
  
  def fullDni {x a}
    (sub: dl.SubsetStx x (full a))
  :
    dl.SubsetStx x (full (compl (compl a)))
  :=
    fullMono sub (dni subId)
  
  def isFullAny {x}:
    dl.SubsetStx x (full any)
  :=
    fullMono (isFullImpl (subId (a := x))) anyI
  
  def isFullOfAny {x a}
    (sub: dl.SubsetStx any a)
  :
    dl.SubsetStx x (full a)
  :=
    mp (fullImplDist (isFullImpl (x:=x) sub)) isFullAny
  
  def isFullImplElim {a b}
    (sub: dl.SubsetStx any (full (impl a b)))
  :
    dl.SubsetStx a b
  :=
    (trans (irI anyI subId) (implAbsorb (fullElim sub)))
  
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
  
  def someI {x a}
    (sub: dl.SubsetStx x a)
  :
    dl.SubsetStx x (some a)
  :=
    complI (irCtxL sub) (irCtxR (fullElim subId))
  
  def someMono {x a b}
    (sub: dl.SubsetStx x (some a))
    (ab: dl.SubsetStx x (full (impl a b)))
  :
    dl.SubsetStx x (some b)
  :=
    byContra (pe
      (fullMp (irCtxL (fullMono ab (contra subId))) (dne subIrR))
      (irCtxL sub))
  
  def someMonoSub {x a b}
    (sub: dl.SubsetStx x (some a))
    (ab: dl.SubsetStx a b)
  :
    dl.SubsetStx x (some b)
  :=
    someMono sub (isFullImpl ab)
  
  def fullImplSome {x a b}
    (sub: dl.SubsetStx x (full (impl a b)))
  :
    dl.SubsetStx x (impl (some a) (some b))
  :=
    implIntro (someMono subIrR (irCtxL sub))
  
  def fullSome {x a}
    (sub: dl.SubsetStx x (full a))
  :
    dl.SubsetStx x (some a)
  :=
    fullElim (fullMono sub (someI subId))
  
  def someAddFull {x a}
    (sub: dl.SubsetStx x (some a))
  :
    dl.SubsetStx x (full (some a))
  :=
    byContra (pe (someStripFull subIrR) (irCtxL sub))
  
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
    byContra (pe (fullDni (fullAddFull (dne subIrR))) (irCtxL sub))
  
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
    complImpl sub.complSomeElim
  
  def someNoneElim {x a}
    (sub: dl.SubsetStx x (some none))
  :
    dl.SubsetStx x a
  :=
    noneElim (sub.trans (arbIrI (subCompl isFullAny)))
  
  def fullMpSome {x f s}
    (sub: dl.SubsetStx x (full (impl (some s) f)))
    (subS: dl.SubsetStx x (some s))
  :
    dl.SubsetStx x (full f)
  :=
    fullMp sub (someAddFull subS)
  
  def fullImplTrans {x a b c}
    (subAb: dl.SubsetStx x (full (impl a b)))
    (subBc: dl.SubsetStx x (full (impl b c)))
  :
    dl.SubsetStx x (full (impl a c))
  :=
    fullMp (fullMono subBc (implAddUnL subId)) subAb
  
  def fullImplOfSome {x s a b}
    (sub: dl.SubsetStx x (full (impl (ir (some s) a) b)))
    (subS: dl.SubsetStx x (some s))
  :
    dl.SubsetStx x (full (impl a b))
  :=
    fullMpSome (fullMono sub (curry subId)) subS
  
  def fullIrDist {x a b}
    (sub: dl.SubsetStx x (full (ir a b)))
  :
    dl.SubsetStx x (ir (full a) (full b))
  :=
    irI (fullMono sub subIrL) (fullMono sub subIrR)
  
  def fullIrDistElim {x a b}
    (sub: dl.SubsetStx x (ir (full a) (full b)))
  :
    dl.SubsetStx x (full (ir a b))
  :=
    fullIr (irL sub) (irR sub)
  
  def someUnDist {x a b}
    (sub: dl.SubsetStx x (some (un a b)))
  :
    dl.SubsetStx x (un (some a) (some b))
  :=
    complI
      (irCtxR
        (fullMono
          (fullIrDistElim (irLR (dne subId) (dne subId)))
          (dni subId)))
      (irCtxL sub)
  
  
  def pairMono {x al bl ar br}
    (sub: dl.SubsetStx x (pair al ar))
    (sl: dl.SubsetStx x (full (impl al bl)))
    (sr: dl.SubsetStx x (full (impl ar br)))
  :
    dl.SubsetStx x (pair bl br)
  :=
    mp (pairMonoFullImpl sl sr).fullElim sub
  
  def pairMonoSub {x al ar bl br}
    (sub: dl.SubsetStx x (pair al ar))
    (sl: dl.SubsetStx al bl)
    (sr: dl.SubsetStx ar br)
  :
    dl.SubsetStx x (pair bl br)
  :=
    pairMono sub (isFullImpl sl) (isFullImpl sr)
  
  def subPairMono {al ar bl br}
    (sl: dl.SubsetStx al bl)
    (sr: dl.SubsetStx ar br)
  :
    dl.SubsetStx (pair al ar) (pair bl br)
  :=
    pairMonoSub subId sl sr
  
  def pairMonoSubL {x a c b}
    (sub: dl.SubsetStx x (pair a b))
    (ac: dl.SubsetStx a c)
  :
    dl.SubsetStx x (pair c b)
  :=
    pairMonoSub sub ac subId
  
  def pairMonoSubR {x a b c}
    (sub: dl.SubsetStx x (pair a b))
    (bc: dl.SubsetStx b c)
  :
    dl.SubsetStx x (pair a c)
  :=
    pairMonoSub sub subId bc
  
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
      ((complPairElim subId).unMonoSubR
        (unMonoSubR subId subUnL))
  
  def pairNoneElimL {x a b}
    (sub: dl.SubsetStx x (pair none a))
  :
    dl.SubsetStx x b
  :=
    pe sub (complPair (unR (unL (pairMonoSub sub anyI anyI))))
  
  def pairNoneElimR {x a b}
    (sub: dl.SubsetStx x (pair a none))
  :
    dl.SubsetStx x b
  :=
    pe sub (complPair (unR (unR (pairMonoSub sub anyI anyI))))
  
  def nullPair {x}:
    dl.SubsetStx x (un null (pair any any))
  :=
    (nullPairComplPair (a := none)).unElim
      (irCtxR subUnL)
      (unElimCont
        (irCtxR ((pairMonoSubL subId anyI).unR))
        (unElimCont
          (irCtxR ((pairMonoSubR subId anyI).unR))
          (irCtxR (pairNoneElimR subId))))
  
  def subSimplePairInduction {a p}
    (sub: dl.SubsetStx (un null (pair p p)) p)
  :
    dl.SubsetStx a p
  :=
    mp (fullElim (simplePairInduction (isFullImpl sub))) subId
  
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
    irI
      (pairMonoSub sub subIrL subId)
      (pairMonoSub sub subIrR subId)
  
  def irPairR {x a b c}
    (sub: dl.SubsetStx x (pair a (ir b c)))
  :
    dl.SubsetStx x (ir (pair a b) (pair a c))
  :=
    irI
      (pairMonoSub sub subId subIrL)
      (pairMonoSub sub subId subIrR)
  
  def irPair {x al ar bl br}
    (sub: dl.SubsetStx x (pair (ir al ar) (ir bl br)))
  :
    dl.SubsetStx x (ir (pair al bl) (pair ar br))
  :=
    irI
      (pairMonoSub sub subIrL subIrL)
      (pairMonoSub sub subIrR subIrR)
  
  def pairComplUnL {x a b c}
    (subA: dl.SubsetStx x (pair (compl a) c))
    (subB: dl.SubsetStx x (pair (compl b) c))
  :
    dl.SubsetStx x (pair (compl (un a b)) c)
  :=
    pairMonoSubL (pairIrL subA subB) (complUnElim subId)
  
  def pairComplUnR {x a b c}
    (subA: dl.SubsetStx x (pair a (compl b)))
    (subB: dl.SubsetStx x (pair a (compl c)))
  :
    dl.SubsetStx x (pair a (compl (un b c)))
  :=
    pairMonoSubR (pairIrR subA subB) (complUnElim subId)
  
  def complPairUnL {x a b c}
    (subA: dl.SubsetStx x (compl (pair a c)))
    (subB: dl.SubsetStx x (compl (pair b c)))
  :
    dl.SubsetStx x (compl (pair (un a b) c))
  :=
    complPair <|
    (complPairElim subA).unElim
      (unL subIrR)
      (subIrR.unElim
        ((irCtxL (irCtxL (complPairElim subB))).unElim
          (unL subIrR)
          (subIrR.unElim
            (unR (unL (pairComplUnL (irR (irL subIrL)) subIrR)))
            (unR (unR subIrR))))
        (unR (unR subIrR)))
  
  def complPairUnR {x a b c}
    (subA: dl.SubsetStx x (compl (pair a b)))
    (subB: dl.SubsetStx x (compl (pair a c)))
  :
    dl.SubsetStx x (compl (pair a (un b c)))
  :=
    complPair <|
    (complPairElim subA).unElim
      (unL subIrR)
      (subIrR.unElim
        (unR (unL subIrR))
        ((irCtxL (irCtxL (complPairElim subB))).unElim
          (unL subIrR)
          (subIrR.unElim
            (unR (unL subIrR))
            (unR (unR (pairComplUnR (irR (irL subIrL)) subIrR))))))
  
  def unPairL {x a b c}
    (sub: dl.SubsetStx x (pair (un a b) c))
  :
    dl.SubsetStx x (un (pair a c) (pair b c))
  :=
    let s := complUn subIrR
    byContra
      (pe (irCtxL sub) (complPairUnL (irL s) (irR s)))
  
  def unPairR {x a b c}
    (sub: dl.SubsetStx x (pair a (un b c)))
  :
    dl.SubsetStx x (un (pair a b) (pair a c))
  :=
    let s := complUn subIrR
    byContra
      (pe (irCtxL sub) (complPairUnR (irL s) (irR s)))
  
  def pairFullL {x a b f}
    (subF: dl.SubsetStx x (full f))
    (subP: dl.SubsetStx x (pair a b))
  :
    dl.SubsetStx x (pair (full f) b)
  :=
    pairMono subP subF.fullAddFull.fullUnR (isFullImpl subId)
  
  def pairFullR {x a b f}
    (subF: dl.SubsetStx x (full f))
    (subP: dl.SubsetStx x (pair a b))
  :
    dl.SubsetStx x (pair a (full f))
  :=
    pairMono subP (isFullImpl subId) subF.fullAddFull.fullUnR
  
  
  def pairSomeL {x a b s}
    (subS: dl.SubsetStx x (some s))
    (subP: dl.SubsetStx x (pair a b))
  :
    dl.SubsetStx x (pair (some s) b)
  :=
    pairMono subP subS.someAddFull.fullUnR (isFullImpl subId)
  
  def pairSomeR {x a b s}
    (subS: dl.SubsetStx x (some s))
    (subP: dl.SubsetStx x (pair a b))
  :
    dl.SubsetStx x (pair a (some s))
  :=
    pairMono subP (isFullImpl subId) subS.someAddFull.fullUnR
  
  def pairSomeElimSomeL {x a b}
    (sub: dl.SubsetStx x (pair (some a) b))
  :
    dl.SubsetStx x (some a)
  :=
    byContra
      (pairNoneElimL
        (pairMonoSubL
          (pairIr (irCtxL sub) (pairFullL (dne subIrR) (irCtxL sub)))
          (pe subIrR subIrL)))
  
  def pairSomeElimSomeR {x a b}
    (sub: dl.SubsetStx x (pair a (some b)))
  :
    dl.SubsetStx x (some b)
  :=
    byContra
      (pairNoneElimR
        (pairMonoSubR
          (pairIr (irCtxL sub) (pairFullR (dne subIrR) (irCtxL sub)))
          (pe subIrR subIrL)))
  
  def pairUnL {x a b c}
    (sub: dl.SubsetStx x (un (pair a c) (pair b c)))
  :
    dl.SubsetStx x (pair (un a b) c)
  :=
    sub.unElim
      (pairMonoSub subIrR subUnL subId)
      (pairMonoSub subIrR subUnR subId)
  
  def pairUnR {x a b c}
    (sub: dl.SubsetStx x (un (pair a b) (pair a c)))
  :
    dl.SubsetStx x (pair a (un b c))
  :=
    sub.unElim
      (pairMonoSub subIrR subId subUnL)
      (pairMonoSub subIrR subId subUnR)
  
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
    someMonoSub (nullFullSome (isFullImpl subId)) subIrL
  
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
            (pairMonoFullImpl
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
            (pairMonoFullImpl
              (isFullImpl subId)
              (fullMono (dne subIrR) subUnL)))
          (pairNoneElimR subId)))
  
  def pairFullElimFullL {x a b}
    (sub: dl.SubsetStx x (pair (full a) b))
  :
    dl.SubsetStx x (full a)
  :=
    someStripFull (somePairElimL (someI sub))
  
  def pairFullElimFullR {x a b}
    (sub: dl.SubsetStx x (pair a (full b)))
  :
    dl.SubsetStx x (full b)
  :=
    someStripFull (somePairElimR (someI sub))
  
  def pairMonoZth {x al bl ar br}
    (sub: dl.SubsetStx x (full (impl (pair al ar) (pair bl br))))
    (subSome: dl.SubsetStx x (some ar))
  :
    dl.SubsetStx x (full (impl al bl))
  :=
    let someP := somePair subIrR (irCtxL subSome)
    let fImplQ :=
      fullSubTransImpl
        (pairMonoSubL subId (dne subIrL))
        (irCtxL sub)
    let fImplR := isFullImpl (pairMonoSub subId subIrR anyI)
    let someQR := someMono someP (fullImplIr fImplQ fImplR)
    byContra
      (someNoneElim (someMonoSub someQR
        (pairNoneElimL
          (pairMonoSubL (pairIrOfIr subId) (pe subIrL subIrR)))))
  
  def pairMonoFst {x al bl ar br}
    (sub: dl.SubsetStx x (full (impl (pair al ar) (pair bl br))))
    (subSome: dl.SubsetStx x (some al))
  :
    dl.SubsetStx x (full (impl ar br))
  :=
    let someP := somePair (irCtxL subSome) subIrR
    let fImplQ := isFullImpl (pairMonoSub subId anyI subIrR)
    let fImplR :=
      fullSubTransImpl
        (pairMonoSubR subId (dne subIrL))
        (irCtxL sub)
    let someQR := someMono someP (fullImplIr fImplQ fImplR)
    byContra
      (someNoneElim (someMonoSub someQR
        (pairNoneElimR
          (pairMonoSubR (pairIrOfIr subId) (pe subIrR subIrL)))))
  
  
  def someVar {x i}:
    dl.SubsetStx x (some (var i))
  :=
    someMonoSub (varFullSome (isFullImpl subId)) subIrL
  
  def varSubsingleton {x i}:
    dl.SubsetStx x (var i).isSubsingleton
  :=
    arbIrI (implIntro (varSomeFull subIrR))
  
  def replaceVar {x i a}
    (sub: dl.SubsetStx x (var i))
    (isSome: dl.SubsetStx x (some (ir (var i) a)))
  :
    dl.SubsetStx x a
  :=
    mp isSome.varSomeFull.fullElim sub
  
  
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
    lift_d1_instantiateVar_eq a ▸ arbIrElimVar 0 sub.toLift
  
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
    (subAb: dl.SubsetStx (ir x.lift a) b)
  :
    dl.SubsetStx x (arbIr b)
  :=
    arbIrI (mpIr (arbIrPop sub) subAb)
  
  def arbIrMonoSub {x a b}
    (sub: dl.SubsetStx x (arbIr a))
    (subAb: dl.SubsetStx a b)
  :
    dl.SubsetStx x (arbIr b)
  :=
    arbIrMono sub (irCtxR subAb)
  
  def pointwise {x a}
    (sub: dl.SubsetStx (ir (var 0) x.lift) a.lift)
  :
    dl.SubsetStx x a
  :=
    let subImpl: dl.SubsetStx x.lift (impl (var 0) a.lift) :=
      implIntro (trans (irSymm subId) sub)
    let unNoneA: dl.SubsetStx x (un none a) :=
      arbIrUnLiftDistR (arbIrI subImpl)
    unElimSub unNoneA (noneElim subId) subId
  
  
  def replaceSingleton {x a b}
    (subExpr: dl.SubsetStx x a)
    (isSome: dl.SubsetStx x (some (ir a b)))
    (isSubsingle: dl.SubsetStx x a.isSubsingleton)
  :
    dl.SubsetStx x b
  :=
    let isSub := irCtxR (arbIrPop isSubsingle)
    let someAV := someI (irI (irCtxR subExpr.toLift) subIrL)
    let fullAV := mp isSub someAV
    let someAB := irCtxR isSome.toLift
    let someVB :=
      someMono someAB (fullMono fullAV (implAddIrR subId))
    pointwise (replaceVar subIrL someVB)
  
  
  def arbUnCtxI {x a}
    (sub: dl.SubsetStx x a.lift)
  :
    dl.SubsetStx (arbUn x) a
  :=
    complSwapCtx (arbIrI (subCompl sub))
  
  def arbUnPopCtx {x a}
    (sub: dl.SubsetStx (arbUn x) a)
  :
    dl.SubsetStx x a.lift
  :=
    subComplElim (arbIrPop (dne (subCompl sub)))
  
  def arbUnI {x a t}
    (isSome: dl.SubsetStx x (some t))
    (isSubsingle: dl.SubsetStx x t.isSubsingleton)
    (sub: dl.SubsetStx x (a.instantiateVar t))
  :
    dl.SubsetStx x (arbUn a)
  :=
    complI
      (irCtxL sub)
      (subIrR.arbIrElim (irCtxL isSome) (irCtxL isSubsingle))
  
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
      (irUnDistL (irLR impl subId)).unElimSub
        subIrL (pe subIrL subIrR)
    
    complElim (arbIrI subYComplA) (irCtxL sub)
  
  def arbUnElim {x a b}
    (sub: dl.SubsetStx x (arbUn a))
    (impl: dl.SubsetStx (ir x.lift a) b.lift)
  :
    dl.SubsetStx x b
  :=
    arbUnElimImpl sub (implIntro impl)
  
  def arbUnLift {x a}
    (sub: dl.SubsetStx x a)
  :
    dl.SubsetStx x (arbUn a.lift)
  :=
    arbUnVarI (liftInst (t := var 0) sub)
  
  def arbUnLiftElim {x a}
    (sub: dl.SubsetStx x (arbUn a.lift))
  :
    dl.SubsetStx x a
  :=
    arbUnElim sub subIrR
  
  def arbUnArbUnElim {x a b}
    (sub: dl.SubsetStx x (arbUn (arbUn a)))
    (impl: dl.SubsetStx (ir x.lift.lift a) b.lift.lift)
  :
    dl.SubsetStx x b
  :=
    arbUnElim sub (arbUnElim subIrR (irMonoCtxL impl subIrL))
  
  def arbUnMono {x a b}
    (sub: dl.SubsetStx x (arbUn a))
    (subAb: dl.SubsetStx (ir x.lift a) b)
  :
    dl.SubsetStx x (arbUn b)
  :=
    complI
      (subIrR.arbIrMono
        (mpIrCompl subIrR (irMonoCtxL subAb (irCtxL subIrL))))
      (irCtxL sub)
  
  def arbUnMonoSub {x a b}
    (sub: dl.SubsetStx x (arbUn a))
    (subAb: dl.SubsetStx a b)
  :
    dl.SubsetStx x (arbUn b)
  :=
    arbUnMono sub (irCtxR subAb)
  
  def arbUnConstI {x a}
    (sub: dl.SubsetStx x a)
  :
    dl.SubsetStx x (arbUn a).lift
  :=
    arbUnPopCtx (arbUnMonoSub subId sub)
  
  
  def complArbIrElim {x a}
    (sub: dl.SubsetStx x (compl (arbIr a)))
  :
    dl.SubsetStx x (arbUn (compl a))
  :=
    complI (arbIrMonoSub subIrR (dne subId)) (irCtxL sub)
  
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
    arbIrI (dne (arbIrPop (dne sub)))
  
  def arbUnUnDist {x a b}
    (sub: dl.SubsetStx x (arbUn (un a b)))
  :
    dl.SubsetStx x (un (arbUn a) (arbUn b))
  :=
    sub.arbUnElim
      (unElim
        subIrR
        (unL (arbUnConstI (irCtxR subId)))
        (unR (arbUnConstI (irCtxR subId))))
  
  def unArbUnDistL {x a b}
    (sub: dl.SubsetStx x (un (arbUn a) b))
  :
    dl.SubsetStx x (arbUn (un a b.lift))
  :=
    sub.unElim
      (arbUnMonoSub (irCtxR subId) subUnL)
      (arbUnMonoSub (arbUnLift (irCtxR subId)) subUnR)
  
  def unArbUnDistR {x a b}
    (sub: dl.SubsetStx x (un a (arbUn b)))
  :
    dl.SubsetStx x (arbUn (un a.lift b))
  :=
    sub.unElim
      (arbUnMonoSub (arbUnLift (irCtxR subId)) subUnL)
      (arbUnMonoSub (irCtxR subId) subUnR)
  
  def unArbUnDist {x a b}
    (sub: dl.SubsetStx x (un (arbUn a) (arbUn b)))
  :
    dl.SubsetStx x (arbUn (arbUn (un a.lift b.lift)))
  :=
    sub.unElim
      ((irCtxR subId).arbUnMonoSub
        (arbUnMonoSub (arbUnLift subId) subUnL))
      ((irCtxR subId).arbUnMonoSub
        (arbUnMonoSub (arbUnLift subId) subUnR))
  
  def arbIrPairL {x a b}
    (sub: dl.SubsetStx x (pair (arbIr a) b))
  :
    dl.SubsetStx x (arbIr (pair a b.lift))
  :=
    arbIrI (pairMonoSub sub.toLift (arbIrPop subId) subId)
  
  def arbIrPairR {x a b}
    (sub: dl.SubsetStx x (pair a (arbIr b)))
  :
    dl.SubsetStx x (arbIr (pair a.lift b))
  :=
    arbIrI (pairMonoSub sub.toLift subId (arbIrPop subId))
  
  def arbUnPairL {x a b}
    (sub: dl.SubsetStx x (pair (arbUn a) b))
  :
    dl.SubsetStx x (arbUn (pair a b.lift))
  :=
    let main := pairMonoSubL (pairArbIrL subId) (dni subId)
    sub.trans <| complSwap <| complPair <|
    unElim
      (unMonoSubR
        (arbIrUnLiftDistL
          (arbIrMonoSub subId (complPairElim subId)))
        (arbIrUnLiftDistR subId))
      (irCtxR subUnL)
      (unElimCont
        (irCtxR (unR (unL main)))
        (irCtxR (unR subUnR)))
  
  def arbUnPairR {x a b}
    (sub: dl.SubsetStx x (pair a (arbUn b)))
  :
    dl.SubsetStx x (arbUn (pair a.lift b))
  :=
    let main := pairMonoSubR (pairArbIrR subId) (dni subId)
    sub.trans <| complSwap <| complPair <|
    unElim
      (unMonoSubR
        (arbIrUnLiftDistL
          (arbIrMonoSub subId (complPairElim subId)))
        (arbIrUnLiftDistL subId))
      (irCtxR subUnL)
      (unElimCont
        (irCtxR (unR subUnL))
        (irCtxR (unR (unR main))))
  
  def pairArbUnL {x a b}
    (sub: dl.SubsetStx x (arbUn (pair a b.lift)))
  :
    dl.SubsetStx x (pair (arbUn a) b)
  :=
    arbUnElim sub (pairMonoSubL subIrR (arbUnPopCtx subId))
  
  def pairArbUnR {x a b}
    (sub: dl.SubsetStx x (arbUn (pair a.lift b)))
  :
    dl.SubsetStx x (pair a (arbUn b))
  :=
    arbUnElim sub (pairMonoSubR subIrR (arbUnPopCtx subId))
  
  def fullArbIrDist {x a}
    (sub: dl.SubsetStx x (full (arbIr a)))
  :
    dl.SubsetStx x (arbIr (full a))
  :=
    arbIrI (fullMono sub.toLift (arbIrPop subId))
  
  def arbIrFullDist {x a}
    (sub: dl.SubsetStx x (arbIr (full a)))
  :
    dl.SubsetStx x (full (arbIr a))
  :=
    fullMono
      (someAddFull (someI sub))
      (arbIrI
        (fullElim
          (someStripFull
            (someMonoSub subId (arbIrPop subId)))))
  
  
  def pairAnyArbUnElim {x}
    (sub: dl.SubsetStx x (pair any any))
  :
    dl.SubsetStx x (arbUn (arbUn (pair (var 1) (var 0))))
  :=
    arbUnMonoSub (arbUnPairL sub) (arbUnPairR subId)
  
  def zthPair {x a b}
    (subB: dl.SubsetStx x (some b))
    (sub: dl.SubsetStx x a)
  :
    dl.SubsetStx x (zth (pair a.lift b.lift))
  :=
    let subBody:
      dl.SubsetStx ((var 0).ir x.lift)
        (ifThen
          (ir
            (pair (var 0) any)
            (instantiateVar
              ((pair a b).lift.lift (0 + 1))
              (var 0)))
          (var 0))
    :=
      lift_lift_eq_one _ ▸
      irI
        (someMonoSub
          (somePair
            (someI (irLR subId (toLift sub)))
            (someMonoSub
              subB.toLift.irCtxR
              (irI anyI subId)))
          (irPair (liftInst subId)))
        subIrL
    pointwise (arbUnVarI subBody)
  
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
            (somePairElimL (someMonoSub subId (pairIrOfIr subId))))))
  
  def fstPair {x a b}
    (subA: dl.SubsetStx x (some a))
    (sub: dl.SubsetStx x b)
  :
    dl.SubsetStx x (fst (pair a.lift b.lift))
  :=
    let subBody:
      dl.SubsetStx ((var 0).ir x.lift)
        (ifThen
          (ir
            (pair any (var 0))
            (instantiateVar
              ((pair a b).lift.lift (0 + 1))
              (var 0)))
          (var 0))
    :=
      lift_lift_eq_one _ ▸
      irI
        (someMonoSub
          (somePair
            (someMonoSub
              subA.toLift.irCtxR
              (irI anyI subId))
            (someI (irLR subId (toLift sub))))
          (irPair (liftInst subId)))
        subIrL
    pointwise (arbUnVarI subBody)
  
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
            (somePairElimR (someMonoSub subId (pairIrOfIr subId))))))
  
  def zthMono {x a b}
      (sub: dl.SubsetStx x (zth a.lift))
      (subAb: dl.SubsetStx x (full (impl a b)))
    :
      dl.SubsetStx x (zth b.lift)
    :=
      sub.arbUnMono
        (irI
          ((irCtxR subIrL).someMono
            (fullMono (irCtxL subAb.toLift) (implAddIrL subId)))
          (irCtxR subIrR))
  
  def projZth {x a b}
    (sub: dl.SubsetStx x (pair a b))
  :
    dl.SubsetStx (zth x.lift) a
  :=
    zthPairElim (zthMono subId (isFullImpl sub))
  
  def fstMono {x a b}
      (sub: dl.SubsetStx x (fst a.lift))
      (subAb: dl.SubsetStx x (full (impl a b)))
    :
      dl.SubsetStx x (fst b.lift)
    :=
      sub.arbUnMono
        (irI
          ((irCtxR subIrL).someMono
            (fullMono (irCtxL subAb.toLift) (implAddIrL subId)))
          (irCtxR subIrR))
  
  def projFst {x a b}
    (sub: dl.SubsetStx x (pair a b))
  :
    dl.SubsetStx (fst x.lift) b
  :=
    fstPairElim (fstMono subId (isFullImpl sub))
  
  def nullArbUnPair {x}:
    dl.SubsetStx x (un null (arbUn (arbUn (pair (var 1) (var 0)))))
  :=
    unMonoSubR nullPair (pairAnyArbUnElim subId)
  
  def arbUnNullPair {x}:
    dl.SubsetStx x (arbUn (arbUn (un null (pair (var 1) (var 0)))))
  :=
    arbUnMonoSub
      (unArbUnDistR nullArbUnPair)
      (unArbUnDistR (a := null) subId)
  
  def projZthCtxElimNull {x a}
    (sub: dl.SubsetStx (zth x.lift) a)
  :
    dl.SubsetStx x (un null (pair a any))
  :=
    let subPair := pairMonoSub subId subId anyI
    arbUnNullPair.arbUnArbUnElim
      (subIrR.unElim
        (irCtxR subUnL)
        (unR
          (pairMonoSub
            (pairIrL
              (pairSomeL
                (someI (irI (irCtxR subPair) (irCtxL subIrL)))
                (irCtxR subPair))
              (irCtxR subPair))
            (sub.arbUnPopCtx.toLift)
            subId)))
  
  def projFstCtxElimNull {x b}
    (sub: dl.SubsetStx (fst x.lift) b)
  :
    dl.SubsetStx x (un null (pair any b))
  :=
    let subPair := pairMonoSub subId anyI subId
    arbUnNullPair.arbUnArbUnElim
      (subIrR.unElim
        (irCtxR subUnL)
        (unR
          (pairMonoSub
            (pairIrR
              (pairSomeR
                (someI (irI (irCtxR subPair) (irCtxL subIrL)))
                (irCtxR subPair))
              (irCtxR subPair))
            subId
            ((lift_lift_eq_one b).symm ▸
              (lift_lift_eq_one x).symm ▸
              sub.arbUnPopCtx.toLift (d := 1)))))
  
  def projZthCtxElim {x a b}
    (sub: dl.SubsetStx (zth x.lift) a)
    (subPair: dl.SubsetStx x (pair any b))
  :
    dl.SubsetStx x (pair a b)
  :=
    (projZthCtxElimNull sub).unElim
      (pe (irCtxL subPair) (complPair (unL subIrR)))
      (pairMonoSub
        (pairIrOfIr (irI subIrR (irCtxL subPair)))
        subIrL subIrR)
  
  def projFstCtxElim {x a b}
    (sub: dl.SubsetStx (fst x.lift) b)
    (subPair: dl.SubsetStx x (pair a any))
  :
    dl.SubsetStx x (pair a b)
  :=
    (projFstCtxElimNull sub).unElim
      (pe (irCtxL subPair) (complPair (unL subIrR)))
      (pairMonoSub
        (pairIrOfIr (irI (irCtxL subPair) subIrR))
        subIrL subIrR)
  
  def pairOfZthFstNull {x a b}
    (subZth: dl.SubsetStx (zth x.lift) a)
    (subFst: dl.SubsetStx (fst x.lift) b)
  :
    dl.SubsetStx x (un null (pair a b))
  :=
    (projZthCtxElimNull subZth).unElim
      (irCtxR subUnL)
      ((irCtxL (projFstCtxElimNull subFst)).unElim
        (irCtxR subUnL)
        (unR (pairMonoSub
          (pairIrOfIr (irI (irCtxL subIrR) subIrR))
          subIrL subIrR)))
  
  def pairOfZthFst {x a b}
    (subZth: dl.SubsetStx (zth x.lift) a)
    (subFst: dl.SubsetStx (fst x.lift) b)
    (subPair: dl.SubsetStx x (pair any any))
  :
    dl.SubsetStx x (pair a b)
  :=
    projZthCtxElim subZth (projFstCtxElim subFst subPair)
  
  def pairZthFst {x e}
    (sub: dl.SubsetStx x e)
    (subPair: dl.SubsetStx x (pair any any))
  :
    dl.SubsetStx x (pair (zth e.lift) (fst e.lift))
  :=
    pairOfZthFst
      (zthMono subId (isFullImpl sub))
      (fstMono subId (isFullImpl sub))
      subPair
  
  def nullPairZthFst {x e}
    (subE: dl.SubsetStx x e)
  :
    dl.SubsetStx x (un null (pair (zth e.lift) (fst e.lift)))
  :=
    pairOfZthFstNull
      (zthMono subId (isFullImpl subE))
      (fstMono subId (isFullImpl subE))
  
end DefList.SubsetStx
