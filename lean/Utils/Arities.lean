inductive ArityZero
inductive ArityOne | zth
inductive ArityTwo | zth | fst

def ArityZero.noInst: ArityZero → False := ArityZero.rec

def ArityZero.elim (az: ArityZero): T := nomatch az

instance ArityOne.ofNatZero: OfNat ArityOne 0 := ⟨ArityOne.zth⟩

instance ArityTwo.ofNatZero: OfNat ArityTwo 0 := ⟨ArityTwo.zth⟩
instance ArityTwo.ofNatOne: OfNat ArityTwo 1 := ⟨ArityTwo.fst⟩
