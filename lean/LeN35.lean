import Mathlib.Tactic.NormNum

def le1: 1 ≤ 35 := by norm_num
def le2: 2 ≤ 35 := by norm_num
def le3: 3 ≤ 35 := by norm_num
def le4: 4 ≤ 35 := by norm_num
def le5: 5 ≤ 35 := by norm_num
def le6: 6 ≤ 35 := by norm_num
def le7: 7 ≤ 35 := by norm_num
def le8: 8 ≤ 35 := by norm_num
def le9: 9 ≤ 35 := by norm_num
def le10: 10 ≤ 35 := by norm_num
def le11: 11 ≤ 35 := by norm_num
def le12: 12 ≤ 35 := by norm_num
def le13: 13 ≤ 35 := by norm_num
def le14: 14 ≤ 35 := by norm_num
def le15: 15 ≤ 35 := by norm_num
def le16: 16 ≤ 35 := by norm_num
def le17: 17 ≤ 35 := by norm_num
def le18: 18 ≤ 35 := by norm_num
def le19: 19 ≤ 35 := by norm_num
def le20: 20 ≤ 35 := by norm_num
def le21: 21 ≤ 35 := by norm_num
def le22: 22 ≤ 35 := by norm_num
def le23: 23 ≤ 35 := by norm_num
def le24: 24 ≤ 35 := by norm_num
def le25: 25 ≤ 35 := by norm_num
def le26: 26 ≤ 35 := by norm_num
def le27: 27 ≤ 35 := by norm_num
def le28: 28 ≤ 35 := by norm_num
def le29: 29 ≤ 35 := by norm_num
def le30: 30 ≤ 35 := by norm_num
def le31: 31 ≤ 35 := by norm_num
def le32: 32 ≤ 35 := by norm_num
def le33: 33 ≤ 35 := by norm_num
def le34: 34 ≤ 35 := by norm_num
def le35: 35 ≤ 35 := by norm_num

def leN35 :=
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
  And.intro le31 (And.intro le32 (And.intro le33 (
  And.intro le34 le35
  )))))))))))))))))))))))))))))))))
