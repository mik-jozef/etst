import Mathlib.Tactic.NormNum

def le1: 1 ≤ 34 := by norm_num
def le2: 2 ≤ 34 := by norm_num
def le3: 3 ≤ 34 := by norm_num
def le4: 4 ≤ 34 := by norm_num
def le5: 5 ≤ 34 := by norm_num
def le6: 6 ≤ 34 := by norm_num
def le7: 7 ≤ 34 := by norm_num
def le8: 8 ≤ 34 := by norm_num
def le9: 9 ≤ 34 := by norm_num
def le10: 10 ≤ 34 := by norm_num
def le11: 11 ≤ 34 := by norm_num
def le12: 12 ≤ 34 := by norm_num
def le13: 13 ≤ 34 := by norm_num
def le14: 14 ≤ 34 := by norm_num
def le15: 15 ≤ 34 := by norm_num
def le16: 16 ≤ 34 := by norm_num
def le17: 17 ≤ 34 := by norm_num
def le18: 18 ≤ 34 := by norm_num
def le19: 19 ≤ 34 := by norm_num
def le20: 20 ≤ 34 := by norm_num
def le21: 21 ≤ 34 := by norm_num
def le22: 22 ≤ 34 := by norm_num
def le23: 23 ≤ 34 := by norm_num
def le24: 24 ≤ 34 := by norm_num
def le25: 25 ≤ 34 := by norm_num
def le26: 26 ≤ 34 := by norm_num
def le27: 27 ≤ 34 := by norm_num
def le28: 28 ≤ 34 := by norm_num
def le29: 29 ≤ 34 := by norm_num
def le30: 30 ≤ 34 := by norm_num
def le31: 31 ≤ 34 := by norm_num
def le32: 32 ≤ 34 := by norm_num
def le33: 33 ≤ 34 := by norm_num
def le34: 34 ≤ 34 := by norm_num

def leN34 :=
  And.intro le1 (And.intro le2 (And.intro le3 (
  And.intro le4 (And.intro le5 (And.intro le6 (
  And.intro le7 (And.intro le8 (And.intro le9 (
  And.intro le10 (And.intro le11 (And.intro le12 (
  And.intro le13 (And.intro le14 (And.intro le15 (
  And.intro le16 (And.intro le17 (And.intro le18 (
  And.intro le19 (And.intro le20 (And.intro le21 (
  And.intro le22 (And.intro le23 (And.intro le24 (
  And.intro le25 (And.intro le26 (And.intro le27 (
  And.intro le28 (And.intro le29 (And.intro le30 (
  And.intro le31 (And.intro le32 (And.intro le33 le34
  ))))))))))))))))))))))))))))))))
