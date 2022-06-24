-- Teorema_de_Cantor.lean
-- Teorema de Cantor.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 6-mayo-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar el teorema de Cantor:
--    ∀ f : α → set α, ¬ surjective f
-- ----------------------------------------------------------------------

import data.set.basic
open function

variables {α : Type}

-- 1ª demostración
-- ===============

example : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f hf,
  let S := {i | i ∉ f i},
  cases hf S with j hj,
  by_cases jS : j ∈ S,
  { apply jS,
    rwa hj, },
  { apply jS,
    rwa ← hj at jS, },
end

-- 2ª demostración
-- ===============

example : ∀ f : α → set α, ¬ surjective f :=
cantor_surjective
