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
    -- `sub.trans` is in general an anti-pattern, but here
    -- it's useful to avoid using `sub` twice (smaller proof).
    sub.trans (irI subIrR subIrL)
  
  def irSymmCtx {l r b}
    (sub: dl.SubsetStx (ir l r) b)
  :
    dl.SubsetStx (ir r l) b
  :=
    trans (irSymm subId) sub
  
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
  
  def subPe {a b}:
    dl.SubsetStx (ir a (compl a)) b
  :=
    pe subIrL subIrR
  
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
  
  
  def subAny {x}:
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
  
  def unCtx {l r b}
    (subL: dl.SubsetStx l b)
    (subR: dl.SubsetStx r b)
  :
    dl.SubsetStx (un l r) b
  :=
    subId.unElim (irCtxR subL) (irCtxR subR)
  
  def em {x a}:
    dl.SubsetStx x (un a a.compl)
  :=
    complI (irCtxR subIrL) (irCtxR subIrR)
  
  def unCtxLR {al ar bl br}
    (subL: dl.SubsetStx al bl)
    (subR: dl.SubsetStx ar br)
  :
    dl.SubsetStx (un al ar) (un bl br)
  :=
    unCtx subL.unL subR.unR
  
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
      (irMonoCtxL subIrL subL)
      (irMonoCtxL subIrL subR)
  
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
          (irMonoCtxL subIrL (implAbsorb subL))
          (irCtxL subIrR))
        (complI
          (irMonoCtxL subIrL (implAbsorb subR))
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
    (irUnDistL sub).trans
      (unCtx
        (trans (irUnDistR subId) (unMonoSubR subId subIrR))
        (irCtxL subUnR))
  
  def unIrDistElimR {x a b c}
    (sub: dl.SubsetStx x (ir (un a b) (un a c)))
  :
    dl.SubsetStx x (un a (ir b c))
  :=
    (irUnDistL sub).trans
      (unCtx
        (irCtxL subUnL)
        (trans (irUnDistR subId) (unMonoSubL subId subIrR)))
  
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
    trans
      (unIrDistElimR (irI subUnR em.unSymm))
      (unCtxLR subId sub)
  
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
        (irMonoCtxR subIrR (implAbsorb sub)))
  
  def implAddIrR {x a b c}
    (sub: dl.SubsetStx x (impl a b))
  :
    dl.SubsetStx x (impl (ir a c) (ir b c))
  :=
    implIntro
      (irI
        (irMonoCtxR subIrL (implAbsorb sub))
        (irCtxR subIrR))
  
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
    mp (trans subAny sub) subId
  
  
  def contra {x a b}
    (sub: dl.SubsetStx x (impl a b))
  :
    dl.SubsetStx x (impl (compl b) (compl a))
  :=
    implIntro
      (mpIrCompl subIrR (irMonoCtxL subIrL (implAbsorb sub)))
  
  def contraElim {x a b}
    (sub: dl.SubsetStx x (impl a.compl b.compl))
  :
    dl.SubsetStx x (impl b a)
  :=
    implIntro
      (mpIrContra subIrR (irMonoCtxL subIrL (implAbsorb sub)))
  
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
  
  def fullSubTransImpl {x b c a}
    (ab: dl.SubsetStx a b)
    (bc: dl.SubsetStx x (full (impl b c)))
  :
    dl.SubsetStx x (full (impl a c))
  :=
    fullMono bc (implIntro (mp subIrL (irCtxR ab)))
  
  def fullImplIr {x a b c}
    (sub1: dl.SubsetStx x (full (impl a b)))
    (sub2: dl.SubsetStx x (full (impl a c)))
  :
    dl.SubsetStx x (full (impl a (ir b c)))
  :=
    let step :=
      implIntro (implIntro (irI
        (mp (irCtxL subIrR) subIrR)
        (mp (irCtxL subIrL) subIrR)))
    fullMp (fullMono sub2 step) sub1
  
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
    mp (fullImplDist (isFullImpl (x:=x) sub)) isFullAny
  
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
    sub.trans (complSwapCtx (someStripFull subId))
  
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
    sub.trans (subCompl (fullMono (fullAddFull subId) (dni subId)))
  
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
  
  def fullMpSome {x f s}
    (sub: dl.SubsetStx x (full (impl (some s) f)))
    (subS: dl.SubsetStx x (some s))
  :
    dl.SubsetStx x (full f)
  :=
    fullMp sub (someAddFull subS)
  
  def fullImplOfSome {x s a b}
    (sub: dl.SubsetStx x (full (impl (ir (some s) a) b)))
    (subS: dl.SubsetStx x (some s))
  :
    dl.SubsetStx x (full (impl a b))
  :=
    fullMpSome (fullMono sub (curry subId)) subS
  
  
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
  
  def pairMonoCtxSubL {x a c b}
    (sub: dl.SubsetStx (pair a b) x)
    (ca: dl.SubsetStx c a)
  :
    dl.SubsetStx (pair c b) x
  :=
    trans (subPairMono ca subId) sub
  
  def pairMonoCtxSubR {x a b c}
    (sub: dl.SubsetStx (pair a b) x)
    (cb: dl.SubsetStx c b)
  :
    dl.SubsetStx (pair a c) x
  :=
    trans (subPairMono subId cb) sub
  
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
    let subPair := pairMonoSub sub subAny subAny
    pe sub (complPair (unR (unL subPair)))
  
  def pairNoneElimR {x a b}
    (sub: dl.SubsetStx x (pair a none))
  :
    dl.SubsetStx x b
  :=
    let subPair := pairMonoSub sub subAny subAny
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
    sub.trans
      (irI
        (subPairMono subIrL subId)
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
        (subPairMono (subIrL.trans (dne subId)) subId)
        (irCtxL sub)
    let fImplR := isFullImpl (subPairMono subIrR subAny)
    let someQR := someMono someP (fullImplIr fImplQ fImplR)
    byContra
      (someNoneElim (someMonoSub someQR
        ((pairIrOfIr subId).trans
          ((subPairMono subPe subId).trans
            (pairNoneElimL subId)))))
  
  def pairMonoFst {x al bl ar br}
    (sub: dl.SubsetStx x (full (impl (pair al ar) (pair bl br))))
    (subSome: dl.SubsetStx x (some al))
  :
    dl.SubsetStx x (full (impl ar br))
  :=
    let someP := somePair (irCtxL subSome) subIrR
    let fImplQ := isFullImpl (subPairMono subAny subIrR)
    let fImplR :=
      fullSubTransImpl
        (subPairMono subId (subIrL.trans (dne subId)))
        (irCtxL sub)
    let someQR := someMono someP (fullImplIr fImplQ fImplR)
    byContra
      (someNoneElim (someMonoSub someQR
        ((pairIrOfIr subId).trans
          ((subPairMono subId (pe subIrR subIrL)).trans
            (pairNoneElimR subId)))))
  
  
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
    pointwise (irI subIrL sub)
  
  
  def replaceSingleton {x a b}
    (subExpr: dl.SubsetStx x a)
    (isSome: dl.SubsetStx x (some (ir a b)))
    (isSubsingle: dl.SubsetStx x a.isSubsingleton)
  :
    dl.SubsetStx x b
  :=
    pointwiseCtx <|
    let isSub := irCtxR (arbIrPop isSubsingle)
    let someAV := someI (irI (irCtxR subExpr.toLift) subIrL)
    let fullAV := mp isSub someAV
    let someAB := irCtxR isSome.toLift
    let someVB :=
      someMono someAB (fullMono fullAV (implAddIrR subId))
    replaceVar subIrL someVB
  
  
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
  
  def arbUnArbUnElim {x a b}
    (sub: dl.SubsetStx x (arbUn (arbUn a)))
    (impl: dl.SubsetStx (ir x.lift.lift a) b.lift.lift)
  :
    dl.SubsetStx x b
  :=
    arbUnElim sub
      (arbUnElim subIrR
        (irMonoCtxL subIrL impl))
  
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
    arbIrI (trans (arbIrPop (dne sub)) (dne subId))
  
  
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
    let main :=
      trans (pairArbIrL subId) (subPairMono (dni subId) subId)
    sub.trans <| complSwap <| complPair <|
    (arbIrMonoSub subId (complPairElim subId))
    |>.trans (arbIrUnLiftDistL subId)
    |>.trans (subId.unCtxLR (arbIrUnLiftDistR subId))
    |>.unElim
      (irCtxR subUnL)
      (unElimCont
        (irCtxR (unR (unL main)))
        (irCtxR (unR subUnR)))
  
  def arbUnPairR {x a b}
    (sub: dl.SubsetStx x (pair a (arbUn b)))
  :
    dl.SubsetStx x (arbUn (pair a.lift b))
  :=
    let main :=
      trans (pairArbIrR subId) (subPairMono subId (dni subId))
    sub.trans <| complSwap <| complPair <|
    (arbIrMonoSub subId (complPairElim subId))
    |>.trans (arbIrUnLiftDistL subId)
    |>.trans (subId.unCtxLR (arbIrUnLiftDistL subId))
    |>.unElim
      (irCtxR subUnL)
      (unElimCont
        (irCtxR (unR subUnL))
        (irCtxR (unR (unR main))))
  
  def pairArbUnL {x a b}
    (sub: dl.SubsetStx x (arbUn (pair a b.lift)))
  :
    dl.SubsetStx x (pair (arbUn a) b)
  :=
    trans sub (arbUnCtxI (subPairMono (arbUnPopCtx subId) subId))
  
  def pairArbUnR {x a b}
    (sub: dl.SubsetStx x (arbUn (pair a.lift b)))
  :
    dl.SubsetStx x (pair a (arbUn b))
  :=
    trans sub (arbUnCtxI (subPairMono subId (arbUnPopCtx subId)))
  
  
  def pairAnyArbUnElim {x}
    (sub: dl.SubsetStx x (pair any any))
  :
    dl.SubsetStx x (arbUn (arbUn (pair (var 1) (var 0))))
  :=
    arbUnMonoSub (arbUnPairL sub) (arbUnPairR subId)
  
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
    let subBody:
      dl.SubsetStx ((var 0).ir (lift x))
        (ifThen
          (ir
            (pair (var 0) any)
            (instantiateVar
              ((pair a b).lift.lift (0 + 1))
              (var 0)))
          (var 0))
    :=
      lift_lift_eq_one _ ▸
      lift_instantiateVar_eq _ _ ▸
      irI
        (someMonoSub
          (somePair
            (someI (irLR subId (toLift sub)))
            (someMonoSub
              subB.toLift.irCtxR
              (irI subAny subId)))
          (irPair subId))
        subIrL
    pointwiseCtx (arbUnVarI subBody)
  
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
    let subBody:
      dl.SubsetStx ((var 0).ir (lift x))
        (ifThen
          (ir
            (pair any (var 0))
            (instantiateVar
              ((pair a b).lift.lift (0 + 1))
              (var 0)))
          (var 0))
    :=
      lift_lift_eq_one _ ▸
      lift_instantiateVar_eq _ _ ▸
      irI
        (someMonoSub
          (somePair
            (someMonoSub
              subA.toLift.irCtxR
              (irI subAny subId))
            (someI (irLR subId (toLift sub))))
          (irPair subId))
        subIrL
    pointwiseCtx (arbUnVarI subBody)
  
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
      (irLR (someMonoSub subId ((irLR subId (toLift sub)))) subId)
  
  def projZth {x a b}
    (sub: dl.SubsetStx x (pair a b))
  :
    dl.SubsetStx (zth x.lift) a
  :=
    zthPairElim (zthMono sub)
  
  def fstMono {x a}
    (sub: dl.SubsetStx x a)
  :
    dl.SubsetStx (fst x.lift) (fst a.lift)
  :=
    subArbUnMono
      (irLR (someMonoSub subId ((irLR subId (toLift sub)))) subId)
  
  def projFst {x a b}
    (sub: dl.SubsetStx x (pair a b))
  :
    dl.SubsetStx (fst x.lift) b
  :=
    fstPairElim (fstMono sub)
  
end DefList.SubsetStx
