/-
Copyright (c) 2026 Gustavo Claassen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Gustavo Claassen
-/
module

import Physlib.SpaceAndTime.Time.Derivatives
import Physlib.Mathematics.Calculus.Gradient
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped Time
open RealInnerProductSpace

/-- Arbitrary system with mass m, position x, and velocity v -/
structure System where
  (m : ℝ)
  (x : Time → EuclideanSpace ℝ (Fin 1))
  (V : Time → EuclideanSpace ℝ (Fin 1) → ℝ)
  m_pos : m > 0

namespace NewtonEqLagrange

variable (S : System)

/-- Definition of kinetic energy and potential energy for the system -/

noncomputable def kineticEnergy : Time → ℝ :=
  fun t => (1 / 2) * S.m * ⟪∂ₜ S.x t, ∂ₜ S.x t⟫

def potentialEnergy : Time → ℝ :=
  fun t => S.V t (S.x t)

/-- Lagrangian

 Definition -/
noncomputable def lagrangian (t : Time) :  ℝ :=
  (1 / 2) * S.m * ⟪∂ₜ S.x t, ∂ₜ S.x t⟫ - S.V t (S.x t)

/-- Showing L = T - V -/
lemma lagrangian_eq_kinetic_minus_potential (t : Time) :
    lagrangian S t = kineticEnergy S t - potentialEnergy S t := by
  rfl

#check (gradient (lagrangian S))

/-- TODO: lemmas for grad_pos and grad_vel, define Eq of Motion,
          state theorem, prove theorem -/

noncomputable def force (t : Time) : EuclideanSpace ℝ (Fin 1) :=
  -gradient (fun x => S.V t x) (S.x t)


end NewtonEqLagrange
