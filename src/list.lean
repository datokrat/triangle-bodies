import data.list.basic data.finsupp.basic data.multiset.basic

variables {α : Type}

def list.to_fn' {n : ℕ}
(l : list α) (h : l.length = n) : fin n → α :=
λ k, l.nth_le k.val (h.symm ▸ k.property)

def list.to_fn
(l : list α) : fin l.length → α :=
λ k, l.nth_le k.val k.property