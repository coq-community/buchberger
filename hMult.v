 Hint Resolve (canonical_multpf _ _ _ _ _ _ _ _ _ cs eqA_dec n ltM ltM_dec os).
Hint Resolve (multpf_disr_pX _ _ _ _ _ _ _ _ _ cs eqA_dec n ltM ltM_dec os).

Notation multpf1 := (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec)
  (only parsing).