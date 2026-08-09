/-
  EvmAsm.Evm64.GasCost

  The two-dimensional Amsterdam gas charge used by the Evm64 model.
  Amsterdam split these charges into separate regular- and state-gas
  accumulators rather than renumbering one total.  The header check therefore
  takes a maximum over the two dimensions (`fork.py:370-375`), while the
  accumulators remain separate (`fork.py:1176-1182`).
  `regular` is the ordinary execution-gas component; `state` is the
  state-gas component (whose units are defined by the caller, for example
  bytes multiplied by the state-gas rate), not a second part of a total.
-/

namespace EvmAsm.Evm64

/-- A gas charge split into the independently accumulated regular- and
state-gas dimensions used by Amsterdam's header check. -/
structure GasCost where
  regular : Nat
  state : Nat
  deriving DecidableEq, Repr

namespace GasCost

/-- Add the two gas dimensions component-wise. -/
instance : Add GasCost where
  add a b :=
    { regular := a.regular + b.regular
      state := a.state + b.state }

/-- The zero charge in both gas dimensions. -/
instance : Zero GasCost where
  zero := { regular := 0, state := 0 }

@[simp] theorem add_regular (a b : GasCost) :
    (a + b).regular = a.regular + b.regular := rfl

@[simp] theorem add_state (a b : GasCost) :
    (a + b).state = a.state + b.state := rfl

@[simp] theorem zero_regular :
    (0 : GasCost).regular = 0 := rfl

@[simp] theorem zero_state :
    (0 : GasCost).state = 0 := rfl

end GasCost
end EvmAsm.Evm64
