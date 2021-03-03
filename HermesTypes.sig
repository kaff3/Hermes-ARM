signature HermesTypes =
sig

  exception Error of string*(int*int)

  val check : Hermes.program -> unit
end
