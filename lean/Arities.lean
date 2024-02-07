inductive ArityZero
inductive ArityOne | zth
inductive ArityTwo | zth | fst

def ArityZero.noInst: ArityZero → False := ArityZero.rec

-- For some strange reason I cannot use ArityZero.rec directly
-- "code generator does not support recursor 'ArityZero.rec' yet, consider using 'match ... with' and/or structural recursion"
def ArityZero.elim (az: ArityZero): T :=
  False.elim (ArityZero.rec az)
