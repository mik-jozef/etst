import Etst.WFC.Ch5_SubsethoodPS

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
    (sub: dl.SubsetStx x (ir b b.compl))
  :
    dl.SubsetStx x a
  :=
    complElimIr (trans subIrL sub)
  
  def subPe {a b}:
    dl.SubsetStx (ir b b.compl) a
  :=
    pe subId
  
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
  
  
  def mp {x a b}
    (xab: dl.SubsetStx x (impl a b))
    (xa: dl.SubsetStx x a)
  :
    dl.SubsetStx x b
  :=
    let nbnc := dni (irI (dni (irCtxL xa)) (irCtxR subId))
    complElim (irCtxL xab) nbnc
  
  def mpIr {x a b}
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
          (trans (irLR subIrL subId) (mpIr subL))
          (irCtxL subIrR))
        (complI
          (trans (irLR subIrL subId) (mpIr subR))
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
  
  def implAbsorb {x a b}
    (subImpl: dl.SubsetStx x (impl a b))
  :
    dl.SubsetStx (ir x a) b
  :=
    irMonoCtxL
      subImpl
      (trans
        (irUnDistL subId)
        (unCtx (trans subIrSymm subPe) subIrL))
  
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
  
  
  
  
  -- Rules using none/any, ignore for now.
  -- def subImplCompl {a}:
  --   dl.SubsetStx (impl a none) (compl a)
  -- :=
  --   unCtx subId subNone

  -- def subComplImpl {a}:
  --   dl.SubsetStx (compl a) (impl a none)
  -- :=
  --   subUnL

  -- def ofImpl {x a}
  --   (sub: dl.SubsetStx any (impl x a))
  -- :
  --   dl.SubsetStx x a
  -- :=
  --   implElimExact (trans subAny sub)
  
end DefList.SubsetStx
