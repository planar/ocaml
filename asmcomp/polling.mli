val instrument_fundecl : future_funcnames:Set.Make(String).t -> Mach.fundecl -> Mach.fundecl
val requires_prologue_poll : future_funcnames:Set.Make(String).t -> Mach.instruction -> bool