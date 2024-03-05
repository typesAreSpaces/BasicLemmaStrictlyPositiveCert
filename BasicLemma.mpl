with(Algebraic, ExtendedEuclideanAlgorithm);
with(SolveTools, SemiAlgebraic);
with(RegularChains, SemiAlgebraicSetTools, PolynomialRing);
with(RegularChains,  RealTriangularize);
with(SemiAlgebraicSetTools, IsContained);
with(Optimization, Maximize, Minimize);

BasicLemma := module() option package;

export lift;

lift := proc(f, g, basis, x)

#local Error_Non_Neg := 0;
local Error_Non_Neg := 1/10000;

ExtendedEuclideanAlgorithm(f, g, x, 's', 't');

local R := PolynomialRing([x]);
local _C := map(poly -> poly >= 0, basis);

# Find N such that
# [X] s + N g > 0 over L1
#local L1 := SemiAlgebraic([op(_C), s <= 0], [x]);
local N := 1;

local lowerbound_L1 := Minimize(s + N*g, [op(_C), s <= 0])[1];
while lowerbound_L1 <= 0 do
  N := 2*N;
  lowerbound_L1 := Minimize(s + N*g, [op(_C), s <= 0])[1];
end do;

local s1 := s + N*g;
local t1 := t - N*f;

# Find positive rational d \in R[x] such that
# [X] d*f*g < 1 on C

local d := 1/(ceil(Maximize(f*g, _C)[1])+1);

# Find positive rational eps so small
# such that 
# [] f > 0
# [] 1 > eps*d*f
# [] eps*t1 + s1*f > 0
# over L2 := { p \in C | g(p) \leq eps }

local upperbound_Eps := min(Maximize(g, _C)[1], 1/Maximize(d*f, _C)[1]);
#print("upperbound_Eps", upperbound_Eps);

local f_lowerbound := Minimize(f, [op(_C), g <= upperbound_Eps])[1];
local comb_lowerbound := Minimize(upperbound_Eps*t1 + s1*f, [op(_C), g <= upperbound_Eps])[1];

#while f_lowerbound <= Error_Non_Neg or comb_lowerbound <= Error_Non_Neg do
  #upperbound_Eps := upperbound_Eps/2;
  #f_lowerbound := Minimize(f, [op(_C), g <= upperbound_Eps])[1];
  #comb_lowerbound := Minimize(upperbound_Eps*t1 + s1*f, [op(_C), g <= upperbound_Eps])[1];
  #print("Search upperbound_Eps", upperbound_Eps);
#end do;
##print("Done searching upperbound_Eps", f_lowerbound, comb_lowerbound);

#local eps := convert(upperbound_Eps, rational);
local eps := 13/14;
print("eps", eps);

# TODO
# Find k so large that
# [] eps*t1 + s1*f > s1*f*(1-eps*d*f)^k over the set { p \in C | g(p) \leq eps } =: L2
# |
# |
# |-> [] log(eps*t1 + s1*f) > log(s1) + log(f) + k log (1-eps*d*f) over the set L2
# |-> [] log(eps*t1 + s1*f) - log(s1) - log(f) > k log (1-eps*d*f) 
# we know 1 > eps*d*f over L2 so 1 > 1 - eps*d*f > 0 => log(1-eps*d*f) < 0 over L2
# |-> [] (log(eps*t1 + s1*f) - log(s1) - log(f))/log (1-eps*d*f) < k

local k := 1000;

local L2 := RealTriangularize([op(_C), g <= eps], R);
local k_condition_1 := RealTriangularize([op(_C), g <= eps, eps*t1 + s1*f > s1*f*(1-eps*d*f)^k ], R);
lprint("check ", [op(_C), g <= eps, eps*t1 + s1*f > s1*f*(1-eps*d*f)^k]);

while not IsContained(L2, k_condition_1, R) do
  k:=k+1;
  print("Searching k", k);
end do;

# [] 1 > s1*f*(1-eps*d*f)^k over the set { p \in C | g(p) \geq eps }
# |
# |
# |-> [] 1 > s1*f*(1-eps*d*f)^k over the set { p \in C | g(p) \qeq eps } =: L3
# |-> [] 0 > log(s1) + log(f) + k log(1-eps*d*f) over the set L3
# |-> [] -(log(s1) + log(f))/log(1-eps*d*f) ? k  over the set L3

local L3 := RealTriangularize([op(_C), g >= eps], R);
local k_condition_2 := RealTriangularize([op(_C), g >= eps, eps*t1 + s1*f > s1*f*(1-eps*d*f)^k ], R);

# So (?) k = max((log(eps*t1 + s1*f) - log(s1) - log(f))/log (1-eps*d*f) over L2, -(log(s1) + log(f))/log(1-eps*d*f) over L3)

#local ok := SemiAlgebraic([op(_C), g <= eps], [x]);
#print("hmm", ok);

#map(
  #proc(interval) 
    #print("hmm 1", Maximize(
      #(log(eps*t1 + s1*f) - log(s1*f))/log(1-eps*d*f), 
      #interval));
  #end proc, ok);

#Maximize((log(eps*t1 + s1*f) - log(s1*f))/log(1-eps*d*f), [op(_C), g <= eps]);
#local ok1 := Maximize(log(eps*t1 + s1*f), [op(_C), g <= eps])[1];
#local ok2 := Minimize(log(s1*f*(1-eps*d*f)), [op(_C), g <= eps])[1];
#print("wot 1", ok1);
#print("wot 2", ok2);
#print("wot 3", -ok1/ok2);

return s, t;
end proc;

end module;
