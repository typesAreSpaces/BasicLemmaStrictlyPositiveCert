$define ENABLE_DEBUGGING    false
$define ENABLE_VERIFICATION false
$define LOG_TIME
$define BUMP_FINDN 1/10

$define DEBUG_EXIT lprint(">> Debugging, getting out"); return 0
$define DEBUG(F, L, y, x) if (y) then lprint(">> Debugging file ", F, " at line ", L); x; end if

$define START_LOG_TIME(X, S) stack_level:=stack_level+1;fd := FileTools:-Text:-Open("log_time.txt", append);local _log_time_S := time();FileTools:-Text:-WriteString(fd, cat("Start: ", X, " ", convert(stack_level, string), "\n"));FileTools:-Text:-Close(fd);
$define END_LOG_TIME(X, S) fd := FileTools:-Text:-Open("log_time.txt", append);FileTools:-Text:-WriteString(fd, cat("End: ", X, " ", convert(stack_level, string), "\nTime: ", convert(time() - _log_time_S, string), "\n"));FileTools:-Text:-Close(fd);stack_level:=stack_level-1;
$define INIT_START_LOG_TIME(X, S) local fd;START_LOG_TIME(X, S)

BasicLemma := module() option package;

local stack_level := -1;

local computeMin;
local bound_info;

local findN;
local findEps;
local findK;

export lift;

# Compute minimum of polynomial poly
# over semialgebraic set S
# S is a finite list of intervals
# poly is a polynomial
    computeMin := proc(S, poly, x)
$ifdef LOG_TIME
        INIT_START_LOG_TIME("computeMin",0)
$endif
        if evalb(S = []) then
$ifdef LOG_TIME
            END_LOG_TIME("computeMin",0)
$endif
            return 0, infinity;
        end if;
    local roots_poly;
    local _num, _denom := 1;
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> poly", poly));

        if type(poly, polynom) then
            _num := poly;
        elif type(poly, ratpoly) then
            _num := numer(poly);
            _denom := denom(poly);
        end if;
        roots_poly := map(sol -> op(sol)[2], RootFinding:-Isolate(_denom*diff(_num, x) - _num*diff(_denom, x)));
    local num_roots := nops(roots_poly);
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> poly", poly));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> roots_poly", roots_poly));
    local curr_point;
    local curr_min := infinity, arg_min;
    local i, j := 1;
    local interval;
        for i from 1 to nops(S) do
            interval := bound_info(x, S[i], 0);
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Current interval", interval));

            if not(subs(x=interval[1], _denom) = 0) then
                curr_point := subs(x=interval[1], _num)/subs(x=interval[1], _denom);
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> curr_point left", curr_point));
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> curr_point left", evalf(curr_point)));
                if evalf(curr_point <= curr_min) then
                    curr_min := curr_point;
                    arg_min := interval[1];
                end if;
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> curr_min left", curr_min));
            end if;

            if not(subs(x=interval[2], _denom) = 0) then
                curr_point := subs(x=interval[2], _num)/subs(x=interval[2], _denom);
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> curr_point right", curr_point));
                if evalf(curr_point <= curr_min) then
                    curr_min := curr_point;
                    arg_min := interval[2];
                end if;
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> curr_min right", curr_min));
            end if;

            while j <= num_roots and evalf(roots_poly[j] < interval[1]) do
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> j @1", j));
                j := j + 1;
            end do;

            while j <= num_roots and evalf(roots_poly[j] < interval[2]) do
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> j @2", j));
                curr_point := subs(x=roots_poly[j], _num)/subs(x=roots_poly[j], _denom);
                if evalf(curr_point <= curr_min) then
                    curr_min := curr_point;
                    arg_min := roots_poly[j];
                end if;
                j := j + 1;
            end do;
        end do;
$ifdef LOG_TIME
        END_LOG_TIME("computeMin",0)
$endif
        return arg_min, curr_min;
    end proc;

    bound_info := proc(x, bound, eps)
$ifdef LOG_TIME
        INIT_START_LOG_TIME("bound_info",0)
$endif
    local i1, i2, j1, j2;
        # This is a bounded bounduality
        if(nops(bound) = 2) then
            i1 := simplify(op(bound[1])[1]);
            i2 := simplify(op(bound[1])[2]);
            j1 := simplify(op(bound[2])[1]);
            j2 := simplify(op(bound[2])[2]);
            if evalb(i1 = x) then
                if evalb(j1 = x) then
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [min(i2, j2)+eps, max(i2, j2)-eps];
                else
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [min(i2, j1)+eps, max(i2, j1)-eps];
                end if;
            else
                if evalb(j1 = x) then
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [min(i1, j2)+eps, max(i1, j2)-eps];
                else
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [min(i1, j1)+eps, max(i1, j1)-eps];
                end if;
            end if;
            # This is an equality or unbounded bounduality
        else
            i1 := simplify(op(bound[1])[1]);
            j1 := simplify(op(bound[1])[2]);
            if type(bound[1], `=`) then
                if evalb(i1 = x) then
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [j1, j1];
                else
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [i1, i1];
                end if;
            end if;
            if type(bound[1], `<=`) then
                if evalb(i1 = x) then
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [-infinity, j1-eps];
                else
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [i1+eps, infinity];
                end if;
            end if;
        end if;
    end proc;

# Find N such that
# - s + N g > 0 over L1 := SemiAlgebraic([op(S), s <= 0], [x]);
    findN := proc(s, f, t, g, basis, x)
$ifdef LOG_TIME
        INIT_START_LOG_TIME("findN", 0)
$endif
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> g", g));
    local arg_min, value_min, N;
    local S := SolveTools:-SemiAlgebraic([op(map(poly -> poly >= 0, basis)), s <= 0], [x]);
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> S", S));
        # This branch means that s is already strictly positive over S
        if evalb(S = []) then
$ifdef LOG_TIME
            END_LOG_TIME("findN",0)
$endif
            return 0;
        else
            # This is because g > 0 over L1
            # hence s + N g > 0 over L1 iff N > -s/g over L1
            # iff N > max_{L1}(-s/g)
            # iff N > -min_{L1}(s/g)
            # iff N = eps - min_{L1}(s/g)  where eps > 0
            # iff N = eps*(-min_{L1}(s/g)) where eps > 1
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> s", s));
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> g", g));
            #N := convert(1/100 + evalf(-computeMin(S, s/g, x)[2]), rational);
            N := (1+1/100)*convert(evalf(-computeMin(S, s/g, x)[2]), rational);
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> basis", basis));
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> N", N));
$ifdef LOG_TIME
            END_LOG_TIME("findN",0)
$endif
            return N;
        end if;
    end proc;

# Find positive rational eps so small
# such that
# - f > 0
# - 1 > eps*delta*f
# - eps*t1 + s1*f > 0
# over L2 := {}
    findEps := proc(delta, s1, f, t1, g, basis, x)
$ifdef LOG_TIME
        INIT_START_LOG_TIME("findEps",0)
$endif
    local eps, top, bot, curr;
    local condition1, condition2, condition3;
    local _basis := map(poly -> poly >= 0, basis);
    local S := SolveTools:-SemiAlgebraic(_basis, [x]);
        top := convert(evalf(-computeMin(S, -g, x)[2]), rational);
        bot := 0;
        curr := (top+bot)/2;
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Max bound for eps", top));
        condition1 := SolveTools:-SemiAlgebraic([op(_basis), g <= curr, f <= 0], [x]) = [];
        condition2 := SolveTools:-SemiAlgebraic([op(_basis), g <= curr, 1 <= curr*delta*f], [x]) = [];
        condition3 := SolveTools:-SemiAlgebraic([op(_basis), g <= curr, curr*t1+s1*f <= 0], [x]) = [];
        while evalb(condition1 and condition2 and condition3) = false do
            top := curr;
            curr := (top + bot)/2;
            condition1 := SolveTools:-SemiAlgebraic([op(_basis), g <= curr, f <= 0], [x]) = [];
            condition2 := SolveTools:-SemiAlgebraic([op(_basis), g <= curr, 1 <= curr*delta*f], [x]) = [];
            condition3 := SolveTools:-SemiAlgebraic([op(_basis), g <= curr, curr*t1+s1*f <= 0], [x]) = [];
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Searching eps", curr));
        end do;
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> eps", curr));
$ifdef LOG_TIME
        END_LOG_TIME("findEps",0)
$endif
        return curr;
    end proc;

# Find k so large that
# - eps*t1 + s1*f > s1*f*(1-eps*delta*f)^k over the set { p \in C | g(p) \leq eps } =: L2
# - 1 > s1*f*(1-eps*delta*f)^k over the set { p \in C | g(p) \geq eps } =: L3
    findK := proc(eps, delta, s1, f, t1, g, basis, x)
$ifdef LOG_TIME
        INIT_START_LOG_TIME("findK",0)
$endif
    local S;
    local less_than_one := 999/1000;
    local k := 0;
    local min_value_cond_1;
    local _arg, _value;
    local _basis := map(poly -> poly >= 0, basis);
$ifdef LOG_TIME
        START_LOG_TIME("findK::condition_1",1)
$endif
        S := SolveTools:-SemiAlgebraic([op(_basis), g <= eps], [x]);
        while true do
            _arg, _value := computeMin(S, -s1*f*(1 - eps*delta*f)^k, x);
            _value := -_value;
            min_value_cond_1 := subs(x=_arg, eps*t1 + s1*f);
            if evalf(_value < min_value_cond_1)  then
$ifdef LOG_TIME
                END_LOG_TIME("findK::condition_1",1)
$endif
                break;
            else
                # Find k such that s1*f*(1-eps*delta*f)^k < eps* t1 + s1*f
                k := ceil(
                    ln(less_than_one *min_value_cond_1/subs(x=_arg, s1*f))
                    /ln(subs(x=_arg, 1 - eps*delta*f)));
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Searching k at first condition", k));
            end if;
        end do;

$ifdef LOG_TIME
        START_LOG_TIME("findK::condition_2",2)
$endif
        S := SolveTools:-SemiAlgebraic([op(_basis), g >= eps], [x]);
        while true do
            _arg, _value := computeMin(S, -s1*f*(1 - eps*delta*f)^k, x);
            _value := -_value;
            if evalf(_value < 1) then
$ifdef LOG_TIME
                END_LOG_TIME("findK::condition_2",2)
$endif

$ifdef LOG_TIME
                END_LOG_TIME("findK",0)
$endif
                return k;
            else
                # Find k such that s1*f*(1-eps*delta*f)^k < 1
                k := ceil(ln(less_than_one/subs(x=_arg, s1*f))/ln(subs(x=_arg, 1 - eps*delta*f)));
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Searching k at second condition", k));
            end if;
        end do;
    end proc;

    lift := proc(f, g, basis, x)
$ifdef LOG_TIME
        INIT_START_LOG_TIME("lift",0)
$endif

        Algebraic:-ExtendedEuclideanAlgorithm(f, g, x, 's', 't');
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> s", s));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> t", t));

    local N := findN(s, f, t, g, basis, x);
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> N", N));

    local s1 := s + N*g;
    local t1 := t - N*f;
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> s1", s1));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> t1", t1));

# Find positive rational d \in R[x] such that
# d*f*g < 1 on C
    local S := SolveTools:-SemiAlgebraic(map(poly -> poly >= 0, basis));
    local delta := convert(-9/10/computeMin(S, -f*g, x)[2], rational);
    # Debugging
    #local delta := 1;
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> delta", delta));

    local eps := findEps(delta, s1, f, t1, g, basis, x);
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> eps", eps));
    local k := findK(eps, delta, s1, f, t1, g, basis, x);
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> k", k));

    local r := s1 * delta * f * sum((1 - delta*f*g)^i, i = 0 .. (k - 1));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> r", r));
    local sigma := s1 - r*g;
    local tau := t1 + r*f;

$ifdef LOG_TIME
        END_LOG_TIME("lift",0)
$endif
        return sigma, tau;
    end proc;

end module;
