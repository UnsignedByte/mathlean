import Mathlean.Algebra.Group


def GInt := Int
def GInt.mk (n: Int) : GInt := n

instance : Mul GInt where
  mul := Int.add

instance : Neg GInt where
  neg := Int.neg

instance : Zero GInt where
  zero := GInt.mk 0

@[simp] theorem mul_add (m n: GInt) : m * n = Int.add m n := rfl

instance : Group GInt where
  id := 0
  mul_assoc := by
    intros a b c
    repeat rw [mul_add]
    repeat rw [Int.add_def]
    rw [Int.add_assoc]
  mul_id := by
    intro a
    rw [mul_add, Int.add_def]
    rw [Int.add_zero]
  id_mul := by
    intro a
    rw [mul_add, Int.add_def]
    rw [Int.zero_add]
  mul_inv := by
    intros a
    exists -a
    rw [mul_add, Int.add_def]
    rw [Int.add_right_neg]
  inv_mul := by
    intro a
    exists -a
    rw [mul_add, Int.add_def]
    rw [Int.add_left_neg]
