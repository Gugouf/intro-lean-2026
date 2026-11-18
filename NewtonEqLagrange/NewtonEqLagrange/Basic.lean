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

/-- Here will be formalized the proof that the Euler-Lagrange
 equation of motion is equivalent to Newton's second law

 i. Introduction

Differently from Newton's law, the Euler-Lagrange equation
is not limited to cartesian coordinates. This is useful for
some sistems where is easier to use a more fitting coordinate
system.

ii. Key result

This study seeks to prove (F = ∂ₜp) ↔ (∂ₜ(∂L/∂v) - ∂L/∂x = 0)
where L is the Lagrangian of the system, p is the momentum and
F is the force. -/

structure System where
  m : ℝ
  /- The mass of the system -/
  m_pos : 0 < m
  /- The mass must be positive -/

variable (S : System)

/-- Defining kinetic and potential energies for any system-/
noncomputable def kineticEnergy (xₜ : Time → EuclideanSpace ℝ (Fin 3)) :
Time → ℝ := fun t =>
  (1 / (2 : ℝ)) * S.m * ⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫

def potentialEnergy (x : EuclideanSpace ℝ (Fin 3))
(V : EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ := V x

/-- Defining the Lagrangian for any system and proving L = T - V -/
noncomputable def lagrangian (t : Time) (x : EuclideanSpace ℝ (Fin 3))
(v : EuclideanSpace ℝ (Fin 3)) (V : EuclideanSpace ℝ (Fin 3) → ℝ)
 : ℝ :=
  1 / (2 : ℝ) * S.m * ⟪v, v⟫ - potentialEnergy x V

lemma lagrangian_eq : lagrangian S = fun t x v V =>
  1 / (2 : ℝ) * S.m * ⟪v, v⟫ - potentialEnergy x V := by
  rfl

lemma lagrangian_eq_kinetic_minus_potential (t : Time)
(xₜ : Time → EuclideanSpace ℝ (Fin 3)) (V : EuclideanSpace ℝ (Fin 3) → ℝ) :
  lagrangian S t (xₜ t) (∂ₜ xₜ t) V =
  kineticEnergy S xₜ t - potentialEnergy (xₜ t) V := by
  rfl

/-- Defining an arbitrary force -/
noncomputable def force (x : EuclideanSpace ℝ (Fin 3))
(V : EuclideanSpace ℝ (Fin 3) → ℝ) : EuclideanSpace ℝ (Fin 3) :=
  -gradient V x

lemma gradient_lagrangian_position_eq (t : Time)
    (x v : EuclideanSpace ℝ (Fin 3))
    (V : EuclideanSpace ℝ (Fin 3) → ℝ) :
    gradient (fun x => lagrangian S t x v V) x = force x V := by
  have h_eq : (fun y : EuclideanSpace ℝ (Fin 3) =>
  lagrangian S t y v V)
      = fun y => 1 / (2 : ℝ) * S.m * ⟪v, v⟫ - V y := by
    funext y; simp only [lagrangian_eq]; rfl
  rw [h_eq, force]
  simp only [gradient, fderiv_const_sub, map_neg]

lemma gradient_lagrangian_velocity_eq (t : Time)
    (x v : EuclideanSpace ℝ (Fin 3))
    (V : EuclideanSpace ℝ (Fin 3) → ℝ) :
    gradient (fun v => lagrangian S t x v V) v = S.m • v := by
    have h_eq : (fun y : EuclideanSpace ℝ (Fin 3) =>
    lagrangian S t x y V) =
      fun y => 1 / (2 : ℝ) * S.m * ⟪y, y⟫ - V x := by
      funext y; simp only [lagrangian_eq]; rfl
    rw [h_eq]
    have h_sq : (fun y : EuclideanSpace ℝ (Fin 3) => 1 / (2 : ℝ) * S.m * ⟪y, y⟫ - V x)
    = fun y => (1 / (2 : ℝ) * S.m) * ‖y‖ ^ 2 - V x := by
      funext y; rw [real_inner_self_eq_norm_sq]
    rw [h_sq]
    have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖ ^ 2)
        (2 • innerSL ℝ v) v := (hasStrictFDerivAt_norm_sq v).hasFDerivAt
    have h2 := (h1.const_mul (1 / (2 : ℝ) * S.m)).sub_const (V x)
    rw [gradient, h2.fderiv]
    apply (InnerProductSpace.toDual ℝ _).injective
    ext w
    simp [innerSL_apply_apply]
    ring

lemma deriv_gradient_lagrangian_velocity_eq
    (x : EuclideanSpace ℝ (Fin 3))
    (v : Time → EuclideanSpace ℝ (Fin 3))
    (V : EuclideanSpace ℝ (Fin 3) → ℝ) (t : Time) :
    ∂ₜ (fun s => gradient (fun u => lagrangian S s x u V) (v s)) t
      = ∂ₜ (fun s => S.m • v s) t := by
  have h : (fun s => gradient (fun u => lagrangian S s x u V) (v s))
      = fun s => S.m • v s := by
    funext s
    exact gradient_lagrangian_velocity_eq S s x (v s) V
  rw [h]

theorem Newton_eq_Lagrange
    (x : EuclideanSpace ℝ (Fin 3))
    (v : Time → EuclideanSpace ℝ (Fin 3))
    (V : EuclideanSpace ℝ (Fin 3) → ℝ) (t : Time) :
    ∂ₜ (fun s => S.m • v s) t = force x V ↔
    ∂ₜ (fun s => gradient (fun u => lagrangian S s x u V) (v s)) t
      - gradient (fun y => lagrangian S t y (v t) V) x = 0 := by
  rw [deriv_gradient_lagrangian_velocity_eq S x v V t]
  rw[gradient_lagrangian_position_eq S t x (v t) V, sub_eq_zero]
