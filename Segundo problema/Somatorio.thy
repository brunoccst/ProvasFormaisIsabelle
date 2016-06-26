theory Somatorio
imports Main
begin

primrec sum:: "nat \<Rightarrow> nat"
  where
    sum01: "sum 0 = 0" |
    sum02: "sum (Suc(n)) = Suc(n)*Suc(n) + sum(n)"

theorem th_sum:"sum(n) =  n div 6 * (n+1)*(2*n+1)"
proof(induct n)
have "sum(0) = 0" by  (simp only:sum01)
also have "... = 0 div 6 * (0+1)*(2*0+1)" by arith
finally show "sum(0) = 0 div 6 * (0+1)*(2*0+1)" by simp
next
fix n0::nat
assume HI:"sum(n0) = n0 div 6 * (n0+1)*(2*n0+1)"
show "sum(Suc n0) = (Suc n0) div 6 * ((Suc n0) + 1)*(2*(Suc n0)+1)"
proof -
have "sum(Suc n0) =  Suc(n0)*Suc(n0) + sum(n0)" by (simp only:sum02)
also have "... = "
qed











 







