$ontext

Numerical simulation code for "Cooperative bargaining to manage invasive
species in jurisdictions with public and private lands," by S.D. Siriwardena,
K.M. Cobourn, G.S. Amacher, and R.G. Haight.

Code version 17 November 2017

$offtext

*************************** PART I: PRELIMINARIES ***************************

$offsymlist offsymxref
option solprint = off;
option reslim = 3600;
option sysout = off;
option limrow = 0;
option limcol = 0;
option nlp = conopt;

set              m 'municipalities' /i,u/
                 t 'time periods' /0*11/
                 t0(t) 'initial period' /0/;

scalars          rho 'discount rate' /0.02/
                 r 'growth rate probability of spread' /0.08/
                 V2barg 'maximum net benefits uninfested public land' /23.50/
                 Vtau0g 'net benefits infested no transfer public land' /4.75/
                 V2barp 'maximum net benefits uninfested private land' /23.50/
                 Vtau0p 'net benefits infested no transfer private land' /16.00/
                 c 'linear parameter net benefit function' /-0.2727/
                 d 'quadratic parameter net benefit function' /-0.0661/
                 p0 'initial probability of spread' /0.5/
                 q1 'proportion public land infested municipality'/0.3/
                 q2 'proportion public land uninfested municipality' /0.3/
                 a 'scale parameter intensive margin function' /0.04/
                 b 'intensive margin function'
                 pi2bar 'upper limit net benefits uninfested municipality'
                 maxben 'pv upper limit uninfested municipality'
                 pi10 'lower limit net benefits infested municipality'
                 pi20 'lower limit net benefits uninfested municipality';
b = -a*log(q1);
pi2bar = q2*V2barg+(1-q2)*V2barp;
pi10 = q1*Vtau0g+(1-q1)*Vtau0p;
pi20 = q2*Vtau0g+(1-q2)*Vtau0p;
display b,pi2bar,pi10,pi20;

*time intervals for model equations
scalars          end 'terminal period';
parameters       tf(t) 'terminal period'
                 tc(t) 'control period'
                 beta(t) 'discount factor';
end = card(t)-1;
tf(t)$((ord(t)-1) eq end) = 1;
tc(t)$((ord(t) le end) and (ord(t) gt 1)) = 1;
beta(t)$tc(t) = 1/((1+rho)**(ord(t)-2));
beta(t)$tf(t) = 1/((1+rho)**(ord(t)-2));
display end,tf,tc,beta;

maxben = sum(t$tc(t), beta(t)*pi2bar);
display maxben;

******************* PART II: SOLVE THE FIRST-BEST PROBLEM *******************

variables        lambda(t) 'costate variable'
                 p(t) 'state variable'
                 tau(t) 'control variable'
                 eta(t) 'lagrangian multiplier control constraint'
                 psi1(t) 'lagrangian multiplier state constraint'
                 psi2(t) 'lagrangian multiplier state constraint'
                 dummy 'dummy objective variable';

*state and control constraints
positive variables p,tau,eta,psi1,psi2;
p.up(t) = 1;

equations
                 lagrange(t) 'optimality condition for control'
                 costate(t) 'path for costate variable'
                 eqm(t) 'equation of motion for p'
                 compslack1(t) 'complementary slackness condition control constraint'
                 compslack2(t) 'complementary slackness condition state constraint'
                 compslack3(t) 'complementary slackness condition state constraint'
                 edummy 'dummy equation';
lagrange(t)$tc(t).. tau(t) =e= (q1*b*lambda(t)-eta(t)-q1*c)/(2*d*q1);
costate(t)$tc(t).. lambda(t) =e= (lambda(t+1)-(pi2bar-pi20)+psi1(t)-psi2(t))/(1+rho-r);
eqm(t)$tc(t).. p(t) =e= (1+r)*p(t-1)-q1*b*tau(t);
compslack1(t)$tc(t).. eta(t)*tau(t) =e= 0;
compslack2(t)$tc(t).. psi1(t)*p(t) =e= 0;
compslack3(t)$tc(t).. psi2(t)*(1-p(t)) =e= 0;
edummy.. dummy =e= 0;

*initial and terminal conditions
lambda.fx(t)$t0(t) = 0;
lambda.fx(t)$tf(t) = 0;
p.fx(t)$t0(t) = p0;
tau.fx(t)$tf(t) = 0;

model eabfb /lagrange,costate,eqm,compslack1,compslack2,compslack3,edummy/;

solve eabfb minimizing dummy using nlp;

*post-optimal parameters
parameters       taufb(t) 'path of transfer payments first best'
                 pfb(t) 'spread probability path first best'
                 pvtaufb 'present value transfer payments first best'
                 jf(m) 'maximized objective function first best solution'
                 tjf 'total welfare first best solution';
taufb(t) = tau.l(t);
pfb(t) = p.l(t);
pvtaufb = sum(t$tc(t), beta(t)*tau.l(t));
jf('i') = sum(t$tc(t), beta(t)*((q1*(Vtau0g+c*tau.l(t)+d*tau.l(t)*tau.l(t)))+(1-q1)*Vtau0p+tau.l(t)));
jf('u') = sum(t$tc(t), beta(t)*((1-p.l(t))*pi2bar+p.l(t)*pi20-tau.l(t)));
tjf = sum(m, jf(m));
display pfb,taufb,pvtaufb,jf,tjf;


****************** PART III: SOLVE THE BARGAINING PROBLEM ******************

*define baseline probability of spread and threat points
parameters       ptau0(t) 'no control path of p'
                 threat(m) 'threat points'
                 uncoord 'uncoordinated outcome'
                 gamma(m) 'bargaining power coefficients' /i 0.5/
                 mu(m) 'Hamiltonian weights'
                 soccostun 'social cost uncoordinated solution';
ptau0(t)$t0(t) = p0;
loop(t$tc(t), ptau0(t) = (1+r)*ptau0(t-1););
ptau0(t)$(ptau0(t) ge 1) = 1;
threat('i') = sum(t$tc(t), beta(t)*pi10);
threat('u') = sum(t$tc(t), beta(t)*((1-ptau0(t))*pi2bar+ptau0(t)*pi20));
uncoord = sum(m, threat(m));
gamma('u') = 1-gamma('i');
soccostun = tjf-uncoord;
display ptau0,threat,uncoord;
display soccostun;

equations
                 lagrangeb(t) 'optimality condition for control with bargaining'
                 costateb(t) 'path for costate variable with bargaining';

lagrangeb(t)$tc(t).. tau(t) =e= (q1*b*lambda(t)-eta(t)+mu('u')-mu('i')*(1+q1*c))/(2*c*q1*mu('i'));
costateb(t)$tc(t).. lambda(t) =e= (lambda(t+1)-mu('u')*(pi2bar-pi20)+psi1(t)-psi2(t))/(1+rho-r);

model eabbrg /lagrangeb,costateb,eqm,compslack1,compslack2,compslack3,edummy/;

*set up loop to solve iteratively for Hamiltonian weights in bargaining problem
sets             iter 'iterations' /1*100/;

scalars          test 'test for convergence'
                 toler 'convergence tolerance';

parameters       jbiter(m,iter) 'maximized objective function inside loop'
                 muold(m,iter) 'initial weights'
                 error(m,iter) 'change in weights';

*initialization
mu(m) = 0.5;
test = 5;
toler = 0.00001;

*loop to convergence across mu and j
loop (iter$(test gt toler),

muold(m,iter) = mu(m);

solve eabbrg minimizing dummy using nlp;

jbiter('i',iter) = sum(t$tc(t), beta(t)*((q1*(Vtau0g+c*tau.l(t)+d*tau.l(t)*tau.l(t)))+(1-q1)*Vtau0p+tau.l(t)));
jbiter('u',iter) = sum(t$tc(t), beta(t)*((1-p.l(t))*pi2bar+p.l(t)*pi20-tau.l(t)));

mu('i') = gamma('i')*((jbiter('i',iter)-threat('i'))**(gamma('i')-1))*((jbiter('u',iter)-threat('u'))**gamma('u'));
mu('u') = gamma('u')*((jbiter('i',iter)-threat('i'))**gamma('i'))*((jbiter('u',iter)-threat('u'))**(gamma('u')-1));

error(m,iter) = (mu(m)-muold(m,iter))*(mu(m)-muold(m,iter));
test = smax(m, error(m,iter));
);

display jbiter,error,test,mu;

*solve for bargaining path given Hamiltonian weights in bargaining problem
solve eabbrg minimizing dummy using nlp;

*post-optimal parameters
parameters       taulb(t) 'lower bound tau for bargaining'
                 tauub(t) 'upper bound tau for bargaining'
                 muratio 'ratio of Hamiltonian weights'
                 pvtaub 'present value transfer payments'
                 jb(m) 'maximized objective function'
                 tjb 'total welfare bargaining solution'
                 soccost 'social cost bargaining solution';

taulb(t)$tc(t) = -q1*(c*tau.l(t)+d*tau.l(t)*tau.l(t));
tauub(t)$tc(t) = (ptau0(t)-p.l(t))*(pi2bar-pi20);

muratio = mu('i')/mu('u');
pvtaub = sum(t$tc(t), beta(t)*tau.l(t));

jb('i') = sum(t$tc(t), beta(t)*((q1*(Vtau0g+c*tau.l(t)+d*tau.l(t)*tau.l(t)))+(1-q1)*Vtau0p+tau.l(t)));
jb('u') = sum(t$tc(t), beta(t)*((1-p.l(t))*pi2bar+p.l(t)*pi20-tau.l(t)));
tjb = sum(m, jb(m));

soccost = tjf-tjb;

display ptau0,threat,uncoord,soccostun;
display pfb,taufb,pvtaufb,jf,tjf;
display p.l,mu,muratio,tau.l,pvtaub,jb,tjb,soccost;
display taulb,tauub;



