#$define ENABLE_VERIFICATION

with(SolveTools, SemiAlgebraic);
with(BasicLemma, lift):

#printlevel := -1;

test := proc(f, g, basis, x)
local sigma, tau;
    sigma, tau := lift(f, g, basis, x);
    lprint(">> Result:");
    lprint(">> sigma", sigma);
    lprint(">> tau", tau);
$ifdef ENABLE_VERIFICATION
    lprint(expand(sigma*f + tau*g));
    lprint(SemiAlgebraic([op(map(poly -> poly >= 0, basis)), sigma <= 0], [x]));
    lprint(SemiAlgebraic([op(map(poly -> poly >= 0, basis)), tau <= 0], [x]));
$endif
end proc;

# ----------
# Terminates
# ----------
#nat := [x+3, (x-2)*(x+1), (x-1)*(x+2), -(x-3)];
#f := 2/3*(x+2)*(x-2);

#test(f, 1+f, nat, x);
#test(f, 2+f, nat, x);
#test(1+f, f, nat, x);
#test(x + 3, -(x-3), nat, x);
# ----------

# Terminates
#test((x+2)*(x-2), 37/6*(x+2)*(x-2)+1, [x+3, (x+2)*(x-1), (x+1)*(x-2), -x+3], x);

# Terminates
#test(x+3, -x+3, [-(x+3)*(x-3)], x);

# Terminates
f := x+3;
g := -(x+2)*(x-1)*(x-13);
test(f, g, [f*g], x);

# Terminates
#basis := [-(x+3)*(x+2)*(x-2)*(x-3)*(x-13)*(x+13)];
#t1 := (x+3)*(x+2);
#t2 := -(x-2)*(x-3)*(x-13)*(x+13);
#t2 := -x^4+5*x^3+163*x^2-845*x+1014;
#test(t1, t2, basis, x);

# Terminates
#f1 := (x+2)*(x-2);
#f2 := 259/1500*(x+2)*(x-2)+1;
#Gfix := [x+3, (x+2)*(x-1), (x+1)*(x-2), -x+3, -(x+3)*(x-3)];
#test(f1, f2, Gfix, x);

#t1 := (x+1)*x^2*(x-1);
#t2 := -(x+2)*(x-2);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := (x+2);
#t2 := -(x+1)*x^2*(x-1)*(x-2);
#test(t1, t2, basis, x);

#basis := [-(x+2)*(x+1)*x^2*(x-1)*(x-2) + 4*x^2*(x+1)^2];
#t1 := (x+1)*x^3;
#t2 := 8+x-x^2;
#test(t1, t2, basis, x);

#t1 := x+2;
#t2 := -(x+1)*(x-1)*(x-2) + 2*(x+2);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := x+2;
#t2 := -(x+1)*(x-1)*(x-2);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := x-1;
#t2 := -(x-2)*(x-4)*(x-7);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := x+3;
#t2 := -(x+2)*(x+1)*(x-1)*(x-2)*(x-3);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := (x+2)*(x+1);
#t2 := -(x+3)*(x-1)*(x-2)*(x-3);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := (x^2+1);
#t2 := -(x+2)*(x+1)*(x-1)*(x-2);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := (x+2);
#t2 := -(x+1)*(x-1)*(x-2)*(x-3)*(x-4);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := -(x+1)*(x-1);
#t2 := -t1;
#basis := [t1, t2];
#test((x+1), -(x-1), basis, x);
#test(-(x+1), (x-1), basis, x);

#t1 := -(x-1)*(x-4);
#t2 := (x-2)*(x-3);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := -(x-4);
#t2 := (x-1);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := -(x-1)*(x-5);
#t2 := (x-2)*(x-4);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := -(x-5);
#t2 := (x-1);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := -(x-1)*(x-10);
#t2 := (x-2)*(x-3);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := -(x+4)*(x-4)*(x-2)*(x-3);
#t2 := (x+1)*(x-1)*(x+2)*(x+3);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := (x+3)*(x+2);
#t2 := (x+1)*(x-1);
#basis := [-(x+4)*(x+3)*(x+2)*(x+1)*(x-1)*(x-2)*(x-3)*(x-4)];
#test(t1, t2, basis, x);

#t1 := (x-31/16);
#t2 := -(x-2)*(x-3)*(x-5);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := x^2;
#t2 := -(x+1)*(x-1);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := (x-2)*(x-4);
#t2 := -(x-1)^3*(x-5)^3;
#basis := [t1*t2];
#test(t1, t2, basis, x);

#p1 := (x-2)^3*(x-3);
#p2 := (x-4)^2;
#test(p1, p2, basis, x);

#t1 := -x*(x-4);
#t2 := (x-1)*(x-3);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#h2 := -(x+3)*(x-3);
#g2 := (x+1)*(x+1/2);
#basis := [g2*h2];
#test(h2, g2, basis, x);

#p1 := (x+1)*(x+1/2);
#p2 := -(x+3)*(x-3);
#basis := [p1*p2];
#test(p1, p2, basis, x);

#p1 := (x-3/4)*(x-1);
##p2 := -(x+2)*(x+1)*x^2*(x-1/2)*(x-2);
#p2 := -(x+2)*(x+1)^3*x^2*(x-1/22)*(x-2);
##p2 := -(x+2)*(x-2);
#basis := [p1*p2];
#test(p1, p2, basis, x);

#b1 := (x+3/4)*(x+1/4);
#b2 := (x+1)*(x+7/8);
#b3 := (x+5/8)*x^2*(x-1/2);
#b4 := (x-3/4)*(x-1);
#lg := (x+3);
#rg := -(x-3);

#test(lg*b2, rg*b1, [lg*b2*rg*b1], x);

#p1 := (x+1/4)*(x-1);
##p2 := -(x+2)*(x+1)*x^2*(x-1/2)*(x-2);
#param1:=-99/100;
#param1:=-999/1000;
#p2 := -(x+2)*(x+1)^3*(x-param1)*(x-2);
##p2 := -(x+2)*(x-2);
#basis := [p1*p2];
#test(p1, p2, basis, x);

#test((x+1)*x^2*(x-1), -(x+2)*(x-2), [-(x+2)*(x+1)*x^2*(x-1)*(x-2)], x); 

#g := -(x+3)*(x+2)*x^2*(x-2)*(x-3);
#test(x+3, -(x+2)*x^2*(x-2)*(x-3), [g], x); 
#test((x+2)*x^2*(x-2), -(x+3)*(x-3), [g], x); 
#test(-(x-3), (x+3)*(x+2)*x^2*(x-2), [g], x); 

#test((x+1), -(x-1), [-(x+1)*(x-1)], x); 

#test((x+3), -(x+2)*(x-2)*(x-3), [-(x+3)*(x+2)*(x-2)*(x-3)], x); 
#test((x+2)*(x-2), -(x+3)*(x-3), [-(x+3)*(x+2)*(x-2)*(x-3)], x); 
#test(-(x-3), (x+2)*(x-2)*(x+3), [-(x+3)*(x+2)*(x-2)*(x-3)], x); 

#test((x+1)^3, -(x-2), [-(x+1)^3*(x-2)], x);
#test(-(x-1)^3, (x+2), [-(x+2)*(x-1)^3], x);
#test((x+1)^3, -(x-1)^3, [-(x+1)^3*(x-1)^3], x);

#test((x+3)*(x-3), -(x+4)*(x-5), [-(x+4)*(x+3)*(x-3)*(x-5)], x);

# Benchmark
#__k := 1/2;
#while evalb(__k <= 10) do
  #__poly := -1;
  #for __i from -2*__k to 2*__k do
    #if __i = 0 then
      #next;
    #end if;
    #__poly := __poly*(x-__i);
  #end do;
  #lprint(__poly);
  #__left := x + 2*__k;
  #__right := -(x - 2*__k);

  #__time_l := time();
  #test(__left, simplify(__poly/__left), [__poly], x);
  #__time_l :=  time() - __time_l;

  #__time_r := time();
  #test(__right, simplify(__poly/__right), [__poly], x);
  #__time_r := time() - __time_r;

  #lprint(">> Input polynomial ", __poly);
  #lprint(">> Left natural generator ", __left);
  #lprint(">> Right natural generator ", __right);
  #lprint(">> Time left natural generator: ", __time_l);
  #lprint(">> Time right natural generator: ", __time_r);

  #__k := __k + 1/2;
#end do;

f := (x+3)*(x-3);
g := -(1/2)*(-4 - 21*x^2 + x^4);

f := (-3 + x)*(3 + x);
g := -(1/216)*(-6 + x)*(6 + x)*(79 + 41*x^2);
test(f, g, [f*g], x);

