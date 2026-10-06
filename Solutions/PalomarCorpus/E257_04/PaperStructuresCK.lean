/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.GenericTailOrbitRigidity
import Solutions.PalomarCorpus.E257_04.Statement

open Filter
open Set

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresCK
export PalomarCorpus.E257_04.Shared (affineBinaryOrbit)

theorem affineBinaryOrbit_transport_def : @affineBinaryOrbit = @Erdos249257.affineBinaryOrbit := by
  first
  | (rfl; done)
  | (simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (with_unfolding_all rfl; done)
  | (unfold affineBinaryOrbit Erdos249257.affineBinaryOrbit; done)
  | (unfold affineBinaryOrbit Erdos249257.affineBinaryOrbit <;> simp only [Erdos249257.affineBinaryOrbit, *]; done)
  | (ext x; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (funext a; fun_induction affineBinaryOrbit a <;> simp only [Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a; induction a <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a; induction a <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a; induction a <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a; simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (funext a b; fun_induction affineBinaryOrbit a b <;> simp only [Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b; induction b <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b; induction a generalizing b <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b; induction b generalizing a <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b; simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (funext a b c; fun_induction affineBinaryOrbit a b c <;> simp only [Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction c <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)

theorem affineBinaryOrbit_sub (a : ℕ → ℤ) (u0 v0 : ℤ) :
    ∀ L : ℕ,
      affineBinaryOrbit a u0 L - affineBinaryOrbit a v0 L =
        (2 : ℤ) ^ L * (u0 - v0) := by
  first
  | exact @Erdos249257.affineBinaryOrbit_sub a u0 v0
    done
  | set_option smartUnfolding false in
    exact @Erdos249257.affineBinaryOrbit_sub a u0 v0
    done
  | simp only [affineBinaryOrbit_transport_def]
    exact @Erdos249257.affineBinaryOrbit_sub a u0 v0
    done
  | simpa only [affineBinaryOrbit_transport_def] using @Erdos249257.affineBinaryOrbit_sub a u0 v0
    done
  | simp only [← affineBinaryOrbit_transport_def] at *
    exact @Erdos249257.affineBinaryOrbit_sub a u0 v0
    done
  | simp only [← affineBinaryOrbit_transport_def] at *
    simpa only [affineBinaryOrbit_transport_def] using @Erdos249257.affineBinaryOrbit_sub a u0 v0
    done
  | simp only [affineBinaryOrbit_transport_def] at *
    exact @Erdos249257.affineBinaryOrbit_sub a u0 v0
    done
  | simp only [affineBinaryOrbit_transport_def] at *
    simpa only [affineBinaryOrbit_transport_def] using @Erdos249257.affineBinaryOrbit_sub a u0 v0
    done
  | apply Erdos249257.affineBinaryOrbit_sub <;> assumption
    done
  | simpa only [affineBinaryOrbit] using Erdos249257.affineBinaryOrbit_sub
    done
  | set_option smartUnfolding false in
    with_unfolding_all exact @Erdos249257.affineBinaryOrbit_sub a u0 v0
    done
  | with_unfolding_all exact @Erdos249257.affineBinaryOrbit_sub a u0 v0
    done

end PalomarCorpus.E257.PaperStructuresCK
