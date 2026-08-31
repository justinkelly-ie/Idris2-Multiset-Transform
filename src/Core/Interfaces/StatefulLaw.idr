module Core.Interfaces.StatefulLaw

import Core.UniverseState
import Core.BoxInt

%default total

||| Typeclass for physical laws that linearly transform universe state
||| while strictly preserving total state capacity (energy/token conservation).
public export
interface ConservedStateTransition (0 law : Type) where
  ||| Linearly steps a universe state to a new state of equal capacity.
  public export
  stepLinear : (1 state : UniverseState vm de dm) -> UniverseState vm de dm

  ||| Structural invariant: total state capacity is strictly conserved.
  public export
  0 capacityInvariant : (st : UniverseState vm de dm) ->
                        totalStateCapacity (stepLinear st) = totalStateCapacity st
