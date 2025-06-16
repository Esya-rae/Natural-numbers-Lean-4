cases x
trivial
cases hx
contrapose! h
intro t
rw [succ_add] at t
apply zero_ne_succ at t
exact t
