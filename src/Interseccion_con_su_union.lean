-- Interseccion_con_su_union.lean
-- Intersección con su unión.lean
-- José A. Alonso Jiménez
-- Sevilla, 26 de abril de 2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    s ∩ (s ∪ t) = s
-- ----------------------------------------------------------------------

import data.set.basic
import tactic
open set

variable {α : Type}
variables s t : set α

-- 1ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext,
  split,
  { intro h,
    dsimp at h,
    exact h.left, },
  { intro xs,
    split,
    { exact xs, },
    { left,
      exact xs, }},
end

-- 2ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext,
  split,
  { intro h,
    exact h.left, },
  { intro xs,
    split,
    { exact xs, },
    { exact or.inl xs, }},
end

-- 3ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext,
  exact ⟨λ h, h.left,
         λ xs, ⟨xs , or.inl xs⟩,⟩,
end

-- 4ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext,
  exact ⟨and.left,
         λ xs, ⟨xs , or.inl xs⟩,⟩,
end

-- 5ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext,
  split,
  { rintros ⟨xs,-⟩,
    exact xs, },
  { intro xs,
    use xs,
    left,
    exact xs, },
end

-- 6ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  apply subset_antisymm,
  { rintros x ⟨xs,-⟩,
    exact xs, },
  { intros x xs,
    exact ⟨xs, or.inl xs⟩, },
end

-- 7ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
inf_sup_self

-- 8ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by fifknish
