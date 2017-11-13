Class with_default (T : Type) (default : T) := defaulted : T.
Global Instance by_default {T} {d} : with_default T d := d.
