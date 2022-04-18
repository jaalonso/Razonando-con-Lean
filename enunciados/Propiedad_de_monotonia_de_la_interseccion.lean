-- Propiedad_de_monotonia_de_la_interseccion.lean
-- Propiedad de monotonía de la intersección.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 18-abril-2022
-- =============================================================================

-- ---------------------------------------------------------------------
-- Demostrar que si
--    s ⊆ t
-- entonces
--    s ∩ u ⊆ t ∩ u
-- ----------------------------------------------------------------------

import data.set.basic
import tactic
open set

variable {α : Type}
variables s t u : set α

-- 1ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
sorry
