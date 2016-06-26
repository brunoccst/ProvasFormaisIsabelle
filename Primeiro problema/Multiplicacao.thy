theory Multiplicacao
imports Main
begin

primrec multacc:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
      where
        multacc01: "multacc 0 n a = a" |
        multacc02: "multacc (Suc(k)) n a = multacc k n (a+n)"
        
fun mult:: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    mult01: "mult n 0 = multacc 0 n 0" |
    mult02: "mult n m = multacc n m 0"

theorem multAcc:"\<forall>x y. multacc(x y z) = x * y + z"

end
