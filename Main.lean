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
    simp[]
    rw [Int.add_assoc]
  mul_id := by
    intro a
    simp[]
  id_mul := by
    intro a
    simp[]
  mul_inv := by
    intros a
    exists -a
    simp[]
    rw [Int.add_right_neg]
  inv_mul := by
    intro a
    exists -a
    simp[]
    rw [Int.add_left_neg]
