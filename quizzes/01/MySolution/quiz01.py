"""
In class we defined the extended lam calc to be

x | lamx.t| t(t2)| n | opr | booleans | if(t1, t2, t3) | Y
"""

### ------ START OF QUESTION 1 ------ ###

def fibo(n):
  return n if n <= 1 else fibo(n-1)+fibo(n-2)

# represent fibo as a lambda-term in Church's lambda-calculus extended with--
# integers, booleans, if-then-else, and some arithmetic operations.

# --- SOLUTION --- #

# I wrote this in the extended lambdacalc syntax we defined in class which I wrote about in my notes to self above
# hope this is an acceptable form since its directly translates to the ml style syntax

# Extended Lambda Calc Representation:
# fib = Y(lamf. lamn. if(n<=1, n, (f(n-1) + f(n-2))))
    # where  Y = lamf.(lamx.f(x(x)))(lamx.f(x(x))) -> note Y F enables F(Y (F)) since it the fixed point

# --- END OF SOLUTION --- #

### ------  END OF QUESTION 1 ------ ###



### ------ START OF QUESTION 2 ------ ###

# Write function for finding prime if number is prime in python, then write the lambda calc equivalent
  
###    ----- SOLUTION -----    ###
def isPrime(n):
    def primeCheck(n, div):
        if n == div:
            return True
        elif (n % div == 0):
            return False
        else:
            return primeCheck(n, div+1)
    return primeCheck(n, 2)

### ----- END OF SOLUTION ----- ###

# Extended Lambda Calc Representation:
# isPrime = lamn. Y (lamf.lamn.lamx. if(n==x, True, if(n % x == 0, False, f(n) (x+1))))   

### ------  END OF QUESTION 2 ------ ###


### ------ START OF QUESTION 3 ------ ###
#Extend term subst in lambda0.py to handle operators

###     ----- SOLUTION -----    ###
# datatype term =
# | TMvar of strn
# | TMlam of (strn, term)
# | TMapp of (term, term)
# | TMint | TMbtf | TMif0 | TMop

class term:
    ctag = ""
    def __str__(self):
        return ("term(" + self.ctag + ")")

class term_var(term):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "TMvar"
    def __str__(self):
        return ("TMvar(" + self.arg1 + ")")

class term_lam(term):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1
        self.arg2 = arg2
        self.ctag = "TMlam"
    def __str__(self):
        return ("TMlam(" + self.arg1 + "," + str(self.arg2) + ")")

class term_app(term):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1
        self.arg2 = arg2
        self.ctag = "TMapp"
    def __str__(self):
        return ("TMapp(" + str(self.arg1) + "," + str(self.arg2) + ")")

class term_int(term):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "TMint"
    def __str__(self):
        return f"TMint({self.arg1})"


# below are the extensions I made
class term_btf(term):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "TMbtf"
    def __str__(self):
        return f"TMbtf({self.arg1})"
    
class term_if0(term):
    def __init__(self, arg1, arg2, arg3):
        self.arg1 = arg1
        self.arg2 = arg2
        self.arg3 = arg3
        self.ctag = "TMif0"

    def __str__(self):
        return f"TMif0({str(self.arg1)}, {str(self.arg2)}, {str(self.arg3)})"
    
class term_op(term):
    #should take a tuple of argument in arg2
    def __init__(self, arg1, arg2):
        if len(arg2) != 2:
            raise TypeError("Did not provide a tuple of size 2 for operator term")
        
        #note sure how it's being tested, using index in case professor tests it with a list
        self.arg1 = arg1
        self.arg2 = arg2[0]
        self.arg3 = arg2[1]
        self.ctag = "TMop"

    def __str__(self):
        return f"TMop({self.arg1}, {self.arg2}, {self.arg3})"
    
def term_subst(tm0, x00, sub):
    def subst(tm0):
        return term_subst(tm0, x00, sub)

    #---extensions---#
    if (tm0.ctag == "TMint"):
        return tm0
    
    if (tm0.ctag == "TMbtf"):
        return tm0
    
    if (tm0.ctag == "TMop"):
        operator = tm0.arg1
        tm1 = tm0.arg2
        tm2 = tm0.arg3
        return term_op(operator, (subst(tm1), subst(tm2)))
    
    if (tm0.ctag == "TMif0"):
        return term_if0(subst(tm0.arg1), subst(tm0.arg2), subst(tm0.arg3))
    #---end of extension---#
    
    if (tm0.ctag == "TMvar"):
        x01 = tm0.arg1
        return sub if (x00==x01) else tm0
    
    if (tm0.ctag == "TMlam"):
        x01 = tm0.arg1
        tm1 = tm0.arg2
        return tm0 if (x00==x01) else term_lam(x01, subst(tm1))
    
    if (tm0.ctag == "TMapp"):
        tm1 = tm0.arg1
        tm2 = tm0.arg2
        return term_app(subst(tm1), subst(tm2))
    raise TypeError(tm0) 

# termtest1 = term_app(term_lam("x", term_if0(term_op("==", ["x", 5]), term_btf(True), term_btf(False)) ), term_int(5))
# print(termtest1)
# var_replacement = term_var("y")
# print(term_subst(termtest1, "x", var_replacement))
# termtest2 = term_if0(term_op("==", (term_var("x"), term_int(2))), term_var("x"), term_btf(False))
# print(termtest2)
# print(term_subst(termtest2, "x", term_var("y")))

### ----- END OF SOLUTION ----- ###


### ------  END OF QUESTION 3 ------ ###
