signature HermesInt =
sig

  exception Error of string*(int*int)

  val run : Hermes.program -> bool -> unit
  val R: Hermes.stat -> Hermes.stat

end
