theory ComprimentoDeLista
imports List
begin
primrec tail_len_c_aux::"'a list\<Rightarrow>nat\<Rightarrow>nat"
where
  tail_len_c_aux01:"tail_len_c_aux [] a = a"|
  tail_len_c_aux02:"tail_len_c_aux (h#T) a = tail_len_c_aux T (Suc(a))"

fun tail_len_c::"'a list\<Rightarrow>nat"
where
  tail_len_c01:"tail_len_c [] = 0"|
  tail_len_c02:"tail_len_c T = tail_len_c_aux T 0"


primrec tail_len_nc::"'a list\<Rightarrow>nat"
where
  tail_len_nc01:"tail_len_nc [] = 0"|
  tail_len_nc02:"tail_len_nc (h#T) = 1 + tail_len_nc T"

theorem tail_len_equi: "tail_len_nc T = tail_len_c T"
proof(induct T)
have "tail_len_nc [] = 0" by (simp only:tail_len_nc01)
also have "... = tail_len_c []" by (simp only:tail_len_c01)
finally show "tail_len_nc [] = tail_len_c []" by simp
next
fix T0::"'a list"
assume HI: "tail_len_nc T0 = tail_len_c T0"
show "\<And>a. tail_len_nc (a#T0) = tail_len_c (a#T0)"
proof -
fix a0::"'a"
have "tail_len_nc (a0#T0) =  1 + tail_len_nc T0" by (simp only:tail_len_nc02)
also have "... = 1 + (tail_len_c T0)" by (simp only:HI)

