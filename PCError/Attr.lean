module

public meta import Lean

/-!
# The `pcerror` tag attribute

The attribute `@[pcerror "TAG"]` records the label `TAG` of the mathematical statement that a
declaration formalizes. It is inert: it has no effect on elaboration.

    @[pcerror "T001"]
    theorem my_result : True := trivial
-/

public meta section

open Lean

/-- `@[pcerror "TAG"]` records the label `TAG` of the mathematical statement that the tagged
declaration formalizes. -/
syntax (name := pcerror) "pcerror " str : attr

initialize Lean.registerBuiltinAttribute {
  name  := `pcerror
  descr := "records the label of the statement a declaration formalizes"
  add   := fun _ _ _ => pure ()
}

end
