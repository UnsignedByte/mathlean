
class Group (G: Type u) extends Mul G where
  id: G
  mul_assoc: ∀ a b c: G, a * (b * c) = (a * b) * c
  mul_id: ∀ a: G, a * id = a
  id_mul: ∀ a: G, id * a = a
  mul_inv: ∀ a: G, ∃ a₁: G, a * a₁ = id
  inv_mul: ∀ a: G, ∃ a₁: G, a₁ * a = id

namespace Group
private theorem inverse_commutative_l (G: Type u) [Group G] : ∀ {g h: G}, g * h = Group.id → h * g = Group.id := by
  intros g h
  intro lhs
  obtain ⟨h₁, h_is_inv⟩ := Group.mul_inv h
  have x := congrArg (fun a => a * h₁) lhs
  simp[] at x
  rw [← Group.mul_assoc] at x
  rw [h_is_inv] at x
  rw [Group.mul_id g] at x
  rw [Group.id_mul h₁] at x
  rw [x]
  apply h_is_inv

@[simp]
theorem inverse_commutative (G: Type u) [Group G] : ∀ {g h: G}, g * h = Group.id ↔ h * g = Group.id := by
  intros g h
  constructor
  repeat exact inverse_commutative_l G

@[simp]
theorem id_unique (G: Type u) [Group G] : ∀ {g i: G}, g * i = g → i = Group.id := by
  intros g i mult
  obtain ⟨h, h_inv⟩ := Group.inv_mul g
  have mult := congrArg (HMul.hMul h) mult
  rw [h_inv, Group.mul_assoc, h_inv] at mult
  rw [Group.id_mul i] at mult
  exact mult

@[simp]
theorem inverse_unique (G: Type u) [Group G] : ∀ {g a b: G}, a * g = Group.id ∧ b * g = Group.id → (a = b) := by
  intros g l r prec
  by_cases eq: l = r
  exact eq
  have associative := Group.mul_assoc l g r
  have left_prec := And.left prec
  have right_prec := And.right prec
  rw [inverse_commutative] at right_prec
  rw [left_prec, right_prec] at associative
  rw [Group.mul_id l, Group.id_mul r] at associative
  contradiction

end Group
