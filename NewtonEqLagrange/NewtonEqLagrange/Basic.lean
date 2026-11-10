/-
Copyright (c) 2026 Gustavo Claassen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Gustavo Claassen
-/


import Physlib.SpaceAndTime.Time.Derivatives
import Physlib.SpaceAndTime.Space.Derivatives.Basic

open scoped Time

/-- Arbitrary system with mass m, position x, and velocity v -/
structure System where
  (m : ℝ)
  (x : Time → EuclideanSpace ℝ (Fin 1))
  (v : Time → EuclideanSpace ℝ (Fin 1))
  (V : Time → EuclideanSpace ℝ (Fin 1) → ℝ)
  m_pos : m > 0

namespace LagrangeEqNewton

variable (S : System)

/-- Definition of Newton's Second Law, kinetic energy, potential energy and Lagrangian for the system -/
def NewtonsSecondLaw
    (F : Time → EuclideanSpace ℝ (Fin 1)) : Prop :=
  ∀ t, F t = S.m • ∂ₜ (S.v) t

noncomputable def kineticEnergy : Time → ℝ :=
  fun t => (1 / 2) * S.m * ‖S.v t‖ ^ 2

noncomputable def potentialEnergy : Time → ℝ :=
  fun t => S.V t (S.x t)

noncomputable def lagrangian : Time → ℝ :=
  fun t => kineticEnergy S t - potentialEnergy S t



end LagrangeEqNewton
