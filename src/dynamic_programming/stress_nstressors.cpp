// **********************************************************************************
// Dynamic programming model of stress response with multiple predators
// **********************************************************************************


//HEADER FILES

#include <cstdlib>
#include <stdio.h>
#include <ctime>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <fstream>
#include <cmath>
#include <random>
#include <vector>
#include <algorithm>
#include <chrono>
#include <cassert>
#include <string>


// constants, type definitions, etc.

using namespace std;

random_device rd;
unsigned seed = rd();

double pLeave[2]{0.0,0.0};   // probability that predator leaves
double pArrive[2]{0.0,0.0};  // probability that predator arrives
double pAttack[2]{0.25,0.5};     // probability that predator attacks if present

double vanish_threshold{1e-06}; // threshold below we consider number solutions to be 0

unsigned long max_t_solver{1000000}; // maximum time before we give up numerically solving things

const double alpha    = 1.0;     // parameter controlling effect of hormone level on pKilled
const double mu0      = 0.002;   // background mortality (independent of hormone level and predation risk)
const double hmin     = 0.3;     // level of hormone that minimises damage
const double hslope   = 20.0;     // slope parameter controlling increase in damage with deviation from hmin

// damage units removed per time step
// this can be (re)set through the command line
double repair      = 1;      
int replicate = 1;

const double K        = 0.001;   // parameter K controlling increase in mortality with damage level
const int maxD        = (1.0-mu0)/K; // maximum damage level
const int maxI        = 100000;   // maximum number of iterations
const int maxT        = 50;     // maximum number of time steps since last saw predator
const int maxH        = 100;     // maximum hormone level
const int skip        = 10;      // interval between print-outs

ofstream outputfile;  // output file
ofstream fwdCalcfile; // forward calculation output file
ofstream attsimfile;  // simulated attacks output file

// random numbers
mt19937 mt(seed); // random number generator
uniform_real_distribution<double> Uniform(0, 1); // real number between 0 and 1 (uniform)

int hormone[maxT+1][maxD+1];          // hormone level (strategy)
double pKilled[maxH+1];               // probability of being killed by an attacking predator
double mu[maxD+1];                    // probability of background mortality, as a function of damage
double dnew[maxD+1][maxH+1];          // new damage level, as a function of previous damage and hormone
//double repro[maxH+1];               // reproductive output
double Wopt[maxT+1][maxD+1];          // fitness immediately after predator has/hasn't attacked, under optimal decision h
double W[maxT+1][maxD+1][maxH+1];     // expected fitness at start of time step, before predator does/doesn't attack
double Wnext[maxT+1][maxD+1][maxH+1]; // expected fitness at start of next time step
double F[maxT+1][maxD+1][maxH+1];     // frequency of individuals at start of time step, before predator does/doesn't attack
double Fnext[maxT+1][maxD+1][maxH+1]; // frequency of individuals at start of next time step
double pPred[3][maxT+1];              // probability predator is present, 
double pPredtplus1[3][maxT+1];              // probability predator is present, 
                                      // 0: predator 1 present, 1: predator 2 present
                                      // 2: both predators present
double predDeaths[maxI];              // frequency of deaths from predator
double damageDeaths[maxI];            // frequency of deaths from damage
double bkgrndDeaths[maxI];            // frequency of deaths from background sources
double totfitdiff;                    // fitness difference between optimal strategy in successive iterations

int i;     // iteration




/* SPECIFY FINAL FITNESS */
void FinalFit()
{
  int t,d,h;

  for (t=1;t<=maxT;t++) // note that Wnext is undefined for t=0 because t=1 if predator has just attacked
  {
    for (h=0;h<=maxH;h++)
    {
      for (d=0;d<maxD;d++)
      {
        Wnext[t][d][h] = 1.0;
      }
      Wnext[t][maxD][h] = 0.0; // dead if at upper damage limit
    }
  }
}

enum pred {
    pred1 = 0,  // only pred 1
    pred2 = 1, // only pred 2 
    pred12 = 2 // both predators present
};

/* CALCULATE PROBABILITY THAT ONE OR BOTH PREDATORS ARE PRESENT */
void PredProb()
{
    // fill everything with initial values
    // we are assuming that all frequencies are equal
    // initially

    double init_freq{1.0 / ( 3.0 * maxT )};

    double sum_freq{0.0};
        
    for (unsigned long tau_idx = 1; 
            tau_idx <= maxT; ++tau_idx)
    {
        sum_freq += pPred[pred1][tau_idx] = init_freq;
        sum_freq += pPred[pred2][tau_idx] = init_freq;
        sum_freq += pPred[pred12][tau_idx] = init_freq;
    }

    assert(sum_freq >= 0.0 - vanish_threshold);
    assert(sum_freq <= 1.0 + vanish_threshold) ;
        
    double attack_prev_timestep[3]{0.0,0.0,0.0};

    // use an Eulerian solver to solve probabilities of predators
    // absent vs present
    for (unsigned long ti = 0; ti < max_t_solver; ++ti)
    {
        attack_prev_timestep[pred1] = 0.0;
        attack_prev_timestep[pred2] = 0.0;
        attack_prev_timestep[pred12] = 0.0;
        
        double prob_attack_tau_minus1{0.0};

        // some summations
        for (unsigned long tau_idx = 2; 
                tau_idx <= maxT; ++tau_idx)
        {
            attack_prev_timestep[pred1] += pPred[pred1][tau_idx - 1] * pAttack[pred1];

            attack_prev_timestep[pred2] += pPred[pred2][tau_idx - 1] * pAttack[pred2];

            attack_prev_timestep[pred12] += pPred[pred12][tau_idx - 1] * 
                (pAttack[pred1] + pAttack[pred2] - pAttack[pred1] * pAttack[pred2]);

            prob_attack_tau_minus1 += attack_prev_timestep[pred1] + attack_prev_timestep[pred2] +
                attack_prev_timestep[pred12];

        }


        // Ppred,1(1) = (1 - lambda_1L) * lambda_2L * sum....
        // + (1 - lambda_1L) (1 - lambda_2A) * sum...
        // + lambda_1A * lambda_2L * sum...
        //
        pPred[pred1][1] = ((1.0 - pLeave[pred1]) * pLeave[pred2] * attack_prev_timestep[pred12]
            + (1.0 - pLeave[pred1]) *  (1.0 - pArrive[pred2]) * attack_prev_timestep[pred1]
            + pArrive[pred1] * pLeave[pred2] * attack_prev_timestep[pred2])/
            prob_attack_tau_minus1;

        pPred[pred2][1] = (pLeave[pred1] * (1.0 - pLeave[pred2]) * attack_prev_timestep[pred12]
            + pLeave[pred1] * pArrive[pred2] * attack_prev_timestep[pred1]
            + (1.0 - pArrive[pred1]) * (1.0 - pLeave[pred2]) * attack_prev_timestep[pred2]) / 
            prob_attack_tau_minus1;

        pPred[pred12][1] = (
                (1.0 - pLeave[pred1]) * (1.0 - pLeave[pred2]) * attack_prev_timestep[pred12]
                + (1.0 - pLeave[pred1]) * pArrive[pred2] * attack_prev_timestep[pred1]
                + pArrive[pred1] * (1.0 - pLeave[pred2]) * attack_prev_timestep[pred2]) / 
            prob_attack_tau_minus1;


        assert(pPred[pred12][1] + pPred[pred1][1] + pPred[pred1][0] <= 1.0 + vanish_threshold);
                
        double prob_no_attack_tau_minus_1;

        for (unsigned long tau_idx = 2; 
                tau_idx <= maxT; ++tau_idx)
        {
            prob_no_attack_tau_minus_1 = 
                pPred[pred12][tau_idx - 1] * (1.0 - pAttack[pred1]) * (1.0 - pAttack[pred2]) +
                pPred[pred1][tau_idx - 1] * (1.0 - pAttack[pred1]) +
                pPred[pred2][tau_idx - 1] * (1.0 - pAttack[pred2]) +
                    (1.0 - pPred[pred1][tau_idx - 1] - 
                     pPred[pred2][tau_idx - 1] - pPred[pred12][tau_idx - 1]);

            pPred[pred1][tau_idx] = ((1.0 - pAttack[pred1]) * (1.0 - pAttack[pred2]) *
                pPred[pred12][tau_idx - 1] * (1.0 - pLeave[pred1]) * pLeave[pred2]
                +
                (1.0 - pAttack[pred1]) * pPred[pred1][tau_idx - 1] * 
                    (1.0 - pLeave[pred1]) * (1.0 - pArrive[pred2])
                +
                (1.0 - pAttack[pred2]) * pPred[pred2][tau_idx - 1] *
                    pArrive[pred1] * pLeave[pred2]
                +
                (1.0 - pPred[pred1][tau_idx - 1] - pPred[pred2][tau_idx - 1] - pPred[pred12][tau_idx - 1]) * pArrive[pred1] * (1.0 - pArrive[pred2])) /
                prob_no_attack_tau_minus_1;

            pPred[pred2][tau_idx] = (
                    (1.0 - pAttack[pred1]) * (1.0 - pAttack[pred2]) * 
                        pPred[pred12][tau_idx - 1] * pLeave[pred1] * (1.0  - pLeave[pred2])
                +
                (1.0 - pAttack[pred1]) * pPred[pred1][tau_idx - 1] * 
                    pLeave[pred1] * pArrive[pred2]
                +
                (1.0 - pAttack[pred2]) * pPred[pred2][tau_idx - 1] * 
                    (1.0 - pArrive[pred1]) * (1.0 - pLeave[pred2])
                +
                (1.0 - pPred[pred1][tau_idx - 1] - pPred[pred2][tau_idx - 1] - pPred[pred12][tau_idx - 1]) *
                    (1.0 - pArrive[pred1]) * pArrive[pred2]
                    ) /
                prob_no_attack_tau_minus_1;
            // chek whether ppred 2 is totally finished, don't think so.

            pPred[pred12][tau_idx] = (
                    (1.0 - pAttack[pred1]) * (1.0 - pAttack[pred2]) * 
                        pPred[pred12][tau_idx - 1] * (1.0 - pLeave[pred1]) * (1.0 - pLeave[pred2])
                        +
                        (1.0 - pAttack[pred1]) * pPred[pred1][tau_idx - 1] * (1.0 - pLeave[pred1]) * pArrive[pred2]
                        +
                        (1.0 - pAttack[pred2]) * pPred[pred2][tau_idx - 1] * pArrive[pred1] * (1.0 - pLeave[pred2])
                        +
                        (1.0 - pPred[pred1][tau_idx - 1] - pPred[pred2][tau_idx - 1] - pPred[pred12][tau_idx - 1]) * pArrive[pred1] * pArrive[pred2]
                    ) / 
                prob_no_attack_tau_minus_1;
        } // end for tau_idx

        bool converged{true};

        for (unsigned int tau_idx{1}; tau_idx <= maxT; ++tau_idx)
        {
            if (pPred[pred1][tau_idx - 1] - pPredtplus1[pred1][tau_idx - 1] >= vanish_threshold)
            {
                converged = false;
            }
            
            if (pPred[pred2][tau_idx - 1] - pPredtplus1[pred2][tau_idx - 1] >= vanish_threshold)
            {
                converged = false;
            }

            if (pPred[pred12][tau_idx - 1] - pPredtplus1[pred12][tau_idx - 1] >= vanish_threshold)
            {
                converged = false;
            }
        }

        if (converged)
        {
            break;
        }

        for (unsigned int tau_idx{1}; tau_idx <= maxT; ++tau_idx)
        {
            pPredtplus1[pred1][tau_idx - 1] = pPred[pred1][tau_idx - 1];
            pPredtplus1[pred2][tau_idx - 1] = pPred[pred2][tau_idx - 1];
            pPredtplus1[pred12][tau_idx - 1] = pPred[pred12][tau_idx - 1];
        }
    } // end for unsigned long ti
} // end PredProb()



/* CALCULATE PROBABILITY OF BEING KILLED BY AN ATTACKING PREDATOR */
void Predation()
{
  int h;

  for (h=0;h<=maxH;h++)
  {
    pKilled[h] = max(0.0,1.0 - pow(double(h)/double(maxH),alpha));
  }
}


/* CALCULATE BACKGROUND MORTALITY */
void Mortality()
{
  int d;

  for (d=0;d<=maxD;d++)
  {
    mu[d] = min(1.0,mu0 + K*double(d)); // mortality increases smoothly to 1.0 at d = maxD
  }
}



/* CALCULATE DAMAGE */
void Damage()
{
  int d,h;

  for (d=0;d<=maxD;d++)
  {
    for (h=0;h<=maxH;h++)
    {
      dnew[d][h] = max(0.0,min(double(maxD),double(d) + hslope*(hmin-(double(h)/double(maxH)))*(hmin-(double(h)/double(maxH))) - repair));
    }
  }
}



/* CALCULATE PROBABILITY OF REPRODUCING */
//void Reproduction()
//{
//  int h;
//
//  for (h=0;h<maxH;h++)
//  {
//    repro[h] = 1.0 - pow(double(h)/double(maxH),beta);
//  }
//}



/* CALCULATE OPTIMAL DECISION FOR EACH t */
void OptDec()
{
  int t,h,d,d1,d2;
  double fitness,ddec;
  double psurvive[3];

  // calculate optimal decision h given current t and d (N.B. t =0 if survived attack)
  for (t=0;t<=maxT;t++)
  {
    for (d=0;d<=maxD;d++)
    {
      Wopt[t][d] = 0.0;
      hormone[t][d] = 0;

      for (h=0;h<=maxH;h++)
      {
        fitness = Wnext[min(maxT,t+1)][d][h]; // fitness as a function of h
        if (fitness>Wopt[t][d])
        {
          Wopt[t][d] = fitness; // overwrite Wopt
          hormone[t][d] = h; // overwrite hormone
        }
      }
    }
  }

  // calculate expected fitness as a function of t, h and d, before predator does/doesn't attack
  for (t=1;t<=maxT;t++) // note that W is undefined for t=0 because t=1 if predator has just attacked
  {
    for (d=0;d<=maxD;d++)
    {
      for (h=0;h<=maxH;h++)
      {
        d1=floor(dnew[d][h]); // for linear interpolation
        d2=ceil(dnew[d][h]); // for linear interpolation
        ddec=dnew[d][h]-double(d1); // for linear interpolation

        // first calculate probability of survival in case predators attack

        // survival in case one or both predators attack
        psurvive[pred12] = pAttack[pred1] * pAttack[pred2] * 
            (1.0 - pKilled[h]) * (1.0 - pKilled[h]) +
            (pAttack[pred1] * (1.0 - pAttack[pred2]) + (1.0 - pAttack[pred1]) * pAttack[pred2]) *
                (1.0 - pKilled[h]);

        // survival when predator 1 is present only
        psurvive[pred1] = pAttack[pred1] * (1.0 - pKilled[h]);

        // survival when predator 2 is present only
        psurvive[pred2] = pAttack[pred2] * (1.0 - pKilled[h]);

        // then calculate the actual fitness recursion
        
        W[t][d][h] = pPred[pred12][t] * psurvive[pred12] * (1.0 - mu[d]) * (1.0 + (1.0 - ddec) * Wopt[0][d1] + ddec * Wopt[0][d2]) // survives attack by two predators
                    + pPred[pred1][t] * psurvive[pred1] * (1.0 - mu[d]) * (1.0 + (1.0 - ddec) * Wopt[0][d1] + ddec * Wopt[0][d2]) // prey survives pred1
                    + pPred[pred2][t] * psurvive[pred2] * (1.0 - mu[d]) * (1.0 + (1.0 - ddec) * Wopt[0][d1] + ddec * Wopt[0][d2]) // prey survives pred2
                    +
                    pPred[pred12][t] * (1.0 - pAttack[pred1]) * (1.0 - pAttack[pred2]) * (1.0 - mu[d]) * (1.0 + (1.0 - ddec) * Wopt[t][d1] + ddec * Wopt[t][d2]) // both predators don't attack
                    +
                    pPred[pred1][t] * (1.0 - pAttack[pred1]) * (1.0 - mu[d]) * (1.0 + (1.0 - ddec) * Wopt[t][d1] + ddec * Wopt[t][d2]) // pred 1 does not attack
                    +
                    pPred[pred2][t] * (1.0 - pAttack[pred2]) * (1.0 - mu[d]) * (1.0 + (1.0 - ddec) * Wopt[t][d1] + ddec * Wopt[t][d2]) // pred 2 does not attack
                    +
                    (1.0 - pPred[pred1][t] - pPred[pred2][t] - pPred[pred12][t]) * (1.0 - mu[d]) * (1.0 + (1.0 - ddec) * Wopt[t][d1] + ddec * Wopt[t][d2]); // no attack

      } // end for h 
    } // end for d
  } // end for t
} // optDec



/* OVERWRITE FITNESS ARRAY FROM PREVIOUS ITERATION */
void ReplaceFit()
{
  int t,h,d;
  double fitdiff;

  fitdiff = 0.0;

  for (t=1;t<=maxT;t++)
  {
    for (d=0;d<=maxD;d++)
    {
      for (h=0;h<=maxH;h++)
      {
        fitdiff = fitdiff + fabs(Wnext[t][d][h]-W[t][d][h]);
        Wnext[t][d][h] = W[t][d][h];
      }
    }
  }

  totfitdiff = fitdiff;

}



/* PRINT OUT OPTIMAL STRATEGY */
void PrintStrat()
{
  int t,d;

  outputfile << "t" << "\t" << "d" << "\t" << "hormone" << endl;

  for (t=0;t<=maxT;t++)
  {
    for (d=0;d<=maxD;d++)
    {
      outputfile << t << "\t" << d << "\t" << hormone[t][d] << endl;
    }
  }
  outputfile << endl;
  outputfile << "nIterations" << "\t" << i << endl;
  outputfile << endl;
}




/* WRITE PARAMETER SETTINGS TO OUTPUT FILE */
void PrintParams()
{
  outputfile << endl << "PARAMETER VALUES" << endl
       << "pLeave: " << "\t" << pLeave << endl
       << "pArrive: " << "\t" << pArrive << endl
       << "pAttack: " << "\t" << pAttack << endl
       << "alpha: " << "\t" << alpha << endl
//       << "beta: " << "\t" << beta << endl
       << "mu0: " << "\t" << mu0 << endl
       << "K: " << "\t" << K << endl
       << "maxI: " << "\t" << maxI << endl
       << "maxT: " << "\t" << maxT << endl
       << "maxD: " << "\t" << maxD << endl
       << "maxH: " << "\t" << maxH << endl
       << "hmin: " << "\t" << hmin << endl
       << "hslope: " << "\t" << hslope << endl
       << "repair: " << "\t" << repair << endl;
}



/* FORWARD CALCULATION TO OBTAIN 
 * PER-TIME-STEP MORTALITY FROM STRESSOR VS. DAMAGE */
void fwdCalc(const string &base_name)
{
  int t,d,h,d1,d2,h1,h2,i,age;
  double ddec{0.0};
  double totSurv{0.0};
  double totPredDeaths{0.0};
  double totDamageDeaths{0.0};
  double totBkgrndDeaths{0.0};
  double ppreddeath_tau{0.0};

  // note that F is undefined for t=0 because t=1 if predator has just attacked
  for (t=1;t<=maxT;t++) 
  {
    for (d=0;d<=maxD;d++)
    {
      for (h=0;h<=maxH;h++)
      {
        F[t][d][h] = 0.0;
        Fnext[t][d][h] = 0.0;
      }
    }
  }
  F[maxT][0][hormone[maxT][0]] = 1.0; // initialise all individuals with zero damage, maxT time steps since last attack and corresponding optimal hormone level

  i = 0; // initialise time-step counter ("age")
  totSurv = 1.0; // initialise total proportion of survivors
  while (totSurv > 0.000001)
  {
      i++;
      predDeaths[i] = 0.0;
      damageDeaths[i] = 0.0;
      bkgrndDeaths[i] = 0.0;
    
      // note that F is undefined for t=0 because t=1 if predator has just attacked
      for (t=1;t<=maxT;t++) 
      {
        for (d=0;d<=maxD;d++)
        {
          for (h=0;h<=maxH;h++)
          {
            d1=floor(dnew[d][h]); // for linear interpolation
            d2=ceil(dnew[d][h]); // for linear interpolation
            ddec=dnew[d][h]-double(d1); // for linear interpolation
            
            // attack
            h1=hormone[0][d1];

            Fnext[1][d1][h1] += F[t][d][h] * (
                pPred[pred12][t]*pAttack[pred1]*pAttack[pred2]*
                (1.0-pKilled[h])*(1.0-pKilled[h])*(1.0-mu[d])
                +
                pPred[pred12][t]*((1-pAttack[pred1])*pAttack[pred2] + pAttack[pred1]*(1 - pAttack[pred2]))*(1.0 - pKilled[h]) * (1.0 - mu[d])
                +
                pPred[pred1][t]*pAttack[pred1]*(1.0 - pKilled[h]) * (1.0 - mu[d]) 
                +
                pPred[pred2][t]*pAttack[pred2]*(1.0 - pKilled[h]) * (1.0 - mu[d])
                ) * (1.0 - ddec);

            h2=hormone[0][d2];
            Fnext[1][d2][h2] += F[t][d][h] * (
                pPred[pred12][t]*pAttack[pred1]*pAttack[pred2]*
                (1.0-pKilled[h])*(1.0-pKilled[h])*(1.0-mu[d])
                +
                pPred[pred12][t]*((1-pAttack[pred1])*pAttack[pred2] + pAttack[pred1]*(1 - pAttack[pred2]))*(1.0 - pKilled[h]) * (1.0 - mu[d])
                +
                pPred[pred1][t]*pAttack[pred1]*(1.0 - pKilled[h]) * (1.0 - mu[d])
                +
                pPred[pred2][t]*pAttack[pred2]*(1.0 - pKilled[h]) * (1.0 - mu[d])
                ) * ddec;

            // no attack
            h1=hormone[min(maxT,t+1)][d1];
            Fnext[min(maxT,t+1)][d1][h1] += F[t][d][h] * (
                pPred[pred12][t]*(1.0 - pAttack[pred1])*(1.0 - pAttack[pred2])*(1.0-mu[d])
                +
                pPred[pred1][t]*(1.0 - pAttack[pred1])*(1.0 - mu[d])
                +
                pPred[pred2][t]*(1.0 - pAttack[pred2])*(1.0 - mu[d])
                +
                (1.0 - (pPred[pred12][t] + pPred[pred1][t] + pPred[pred2][t])) * (1.0 - mu[d])
                ) * (1.0 - ddec);

            h2=hormone[min(maxT,t+1)][d2];
            Fnext[min(maxT,t+1)][d2][h2] += F[t][d][h] * (
                pPred[pred12][t]*(1.0 - pAttack[pred1])*(1.0 - pAttack[pred2])*(1.0-mu[d])
                +
                pPred[pred1][t]*(1.0 - pAttack[pred1])*(1.0 - mu[d])
                +
                pPred[pred2][t]*(1.0 - pAttack[pred2])*(1.0 - mu[d])
                +
                (1.0 - (pPred[pred12][t] + pPred[pred1][t] + pPred[pred2][t])) * (1.0 - mu[d])
                ) * ddec;

            ppreddeath_tau = 
                    pPred[pred12][t]*pAttack[pred1]*pAttack[pred2]*(1.0 - (1.0 - pKilled[h]) * (1.0 - pKilled[h]))
                    +
                    pPred[pred12][t]*(pAttack[pred1]*(1.0 - pAttack[pred2]) + (1.0 - pAttack[pred1]* pAttack[pred2]))* pKilled[h]
                    +
                    pPred[pred1][t]*pAttack[pred1]*pKilled[h]
                    +
                    pPred[pred2][t]*pAttack[pred2]*pKilled[h];
            
            // deaths from predation and damage
            predDeaths[i] += F[t][d][h]*ppreddeath_tau;

            damageDeaths[i] += F[t][d][h]*(1.0-ppreddeath_tau)*(mu[d]-mu[0]);
            bkgrndDeaths[i] += F[t][d][h]*(1.0-ppreddeath_tau)*mu[0];
          }
        }
      }

      // OVERWRITE FREQUENCIES
      for (t=1;t<=maxT;t++)
      {
        for (d=0;d<=maxD;d++)
        {
          for (h=0;h<=maxH;h++)
          {
            F[t][d][h] = Fnext[t][d][h]; // next time step becomes this time step
            Fnext[t][d][h] = 0.0; // wipe next time step
          }
        }
      }

      totPredDeaths += predDeaths[i]; // update total deaths due to predation
      totDamageDeaths += damageDeaths[i]; // update total deaths due to damage
      totBkgrndDeaths += bkgrndDeaths[i]; // update total deaths due to background causes

      totSurv = totSurv - predDeaths[i] - damageDeaths[i] - bkgrndDeaths[i]; // update total proportion of survivors

      if (i%skip==0)
      {
        cout << i << "\t" << totSurv << endl; // show total proportion of survivors every 'skip' time steps
      }

  }

  string fwdCalcfilename = "fwdCalc" + base_name + ".txt";
//  fwdCalcfilename += ".txt";
  fwdCalcfile.open(fwdCalcfilename.c_str());
  ///////////////////////////////////////////////////////

  fwdCalcfile << "SUMMARY STATS" << endl
    << "predDeaths/i: " << "\t" << totPredDeaths/i << endl
    << "damageDeaths/i: " << "\t" << totDamageDeaths/i << endl
    << "bkgrndDeaths/i: " << "\t" << totBkgrndDeaths/i << endl
    << endl;

  fwdCalcfile << "\t" << "timestep" << "\t" << "predDeaths" << "\t" << "damageDeaths" << "\t" << "bkgrndDeaths" << endl; // column headings in output file

  for (age=0;age<=i;age++)
    {
      fwdCalcfile << "\t" << age << "\t" << predDeaths[age] << "\t" << damageDeaths[age] << "\t" << bkgrndDeaths[age] << "\t" << endl; // print data
    }

  fwdCalcfile.close();
} // end fWdcalc



/* Simulated series of attacks */
void SimAttacks(const string &base_name)
{
  int i,time,t,d,h,d1,d2;
  const int nInd = 100;
  double ddec,hprop;
  bool attack[100+1];
  double sumD[100+1],sumsqD[100+1],sumH[100+1],sumsqH[100+1],
    meanD[100+1],varD[100+1],meanH[100+1],varH[100+1]; // arrays for stats, from time step 0 to 100

  string attsimfilename = "simAttacks" + base_name;
    attsimfilename += ".txt";

  attsimfile.open(attsimfilename.c_str());
  ///////////////////////////////////////////////////////

  attsimfile << "ACUTE STRESS" << endl;
  attsimfile << "time" << "\t" << "attack" << "\t" << "t" << "\t" << "damage" << "\t" << "sd(damage)" << "\t" << "hormone" << "\t" << "sd(hormone)" << "\t" << endl; // column headings in output file


  for (time=0;time<=50;time++) // wipe stats arrays
  {
     sumD[time+1] = 0.0;
     sumsqD[time+1] = 0.0;
     sumH[time+1] = 0.0;
     sumsqH[time+1] = 0.0;
  }

  for (i=1;i<=nInd;i++) // simulate nInd individuals
  {
    // initialise individual (alive, no damage, no offspring, baseline hormone level) and starting environment (predator)
    time = 0;
    t = maxT;
    d = 0;
    //    r = 0.0;
    h = hormone[t][d];

    while (time <= 50)
    {
        if (time == 10) // predator attacks
        {
          t = 0;
          attack[time+1] = true;
        }
        else
        {
          t++;
          t = min(t,maxT);
          attack[time+1] = false;
        }
        h = hormone[t][d];
        d1 = floor(dnew[d][h]);
        d2 = ceil(dnew[d][h]);
        ddec = dnew[d][h]-d1;
        if (Uniform(mt)<ddec) d = d2; else d = d1;
        sumD[time+1] += d;
        sumsqD[time+1] += d*d;
        hprop = double(h)/double(maxH);
        sumH[time+1] += hprop;
        sumsqH[time+1] += hprop*hprop;
        time++;
    }

  }

  for (time=0;time<=50;time++) // run through time steps
  {
    meanD[time+1] = sumD[time+1]/double(nInd);
    varD[time+1] = sumsqD[time+1]/double(nInd)-meanD[time+1]*meanD[time+1];
    meanH[time+1] = sumH[time+1]/double(nInd);
    varH[time+1] = sumsqH[time+1]/double(nInd)-meanH[time+1]*meanH[time+1];
    attsimfile << time << "\t" << attack[time+1] << "\t" << t << "\t" << meanD[time+1] << "\t" << sqrt(varD[time+1]) << "\t" << meanH[time+1] << "\t" << sqrt(varH[time+1]) << "\t" << endl; // print data
  }

  attsimfile << endl;
  attsimfile << "CHRONIC STRESS" << endl;
  attsimfile << "time" << "\t" << "attack" << "\t" << "t" << "\t" << "damage" << "\t" << "sd(damage)" << "\t" << "hormone" << "\t" << "sd(hormone)" << "\t" << endl; // column headings in output file

  for (time=0;time<=100;time++) // wipe stats arrays
  {
     sumD[time] = 0.0;
     sumsqD[time] = 0.0;
     sumH[time] = 0.0;
     sumsqH[time] = 0.0;
  }

  for (i=1;i<=nInd;i++) // simulate nInd individuals
  {
      // initialise individual (alive, no damage, no offspring, baseline hormone level) and starting environment (predator)
      time = 0;
      t = maxT;
      d = 0;
      //    r = 0.0;
      h = hormone[t][d];

      while (time < 100)
      {
        if (time > 10) // predator attacks
        {
          t = 0;
          attack[time+1] = true;
        }
        else
        {
          t++;
          t = min(t,maxT);
          attack[time+1] = false;
        }
        h = hormone[t][d];
        d1 = floor(dnew[d][h]);
        d2 = ceil(dnew[d][h]);
        ddec = dnew[d][h]-d1;
        if (Uniform(mt)<ddec) d = d2; else d = d1;
        sumD[time+1] += d;
        sumsqD[time+1] += d*d;
        hprop = double(h)/double(maxH);
        sumH[time+1] += hprop;
        sumsqH[time+1] += hprop*hprop;
        time++;
      }
  }

  for (time=0;time<100;time++) // run through time steps
  {
    meanD[time+1] = sumD[time+1]/double(nInd);
    varD[time+1] = sumsqD[time+1]/double(nInd)-meanD[time+1]*meanD[time+1];
    meanH[time+1] = sumH[time+1]/double(nInd);
    varH[time+1] = sumsqH[time+1]/double(nInd)-meanH[time+1]*meanH[time+1];
    attsimfile << time << "\t" << attack[time+1] << "\t" << t << "\t" << meanD[time+1] << "\t" << sqrt(varD[time+1]) << "\t" << meanH[time+1] << "\t" << sqrt(varH[time+1]) << "\t" << endl; // print data
  }

  attsimfile.close();

}



/* MAIN PROGRAM */
int main(int argc, char **argv)
{
    double autocorr[2]{0.0,0.0};
    double risk[2]{0.0,0.0};

    autocorr[0] = atof(argv[1]);
    autocorr[1] = atof(argv[2]);
    
    risk[0] = atof(argv[3]);
    risk[1] = atof(argv[4]);

    repair = atof(argv[5]);

    assert(repair <= maxD);
    replicate = atoi(argv[6]);

    pAttack[0] = atof(argv[7]);
    pAttack[1] = atof(argv[8]);

    std::string base_name{argv[9]};

    // use autocorrelation and risk to calculate pLeave
    // and pArrive for each predator
    for (unsigned pred_idx{0}; pred_idx < 2; ++pred_idx)
    {
        pLeave[pred_idx] = (1.0 - autocorr[pred_idx])/
            (1.0+(risk[pred_idx]/(1.0-risk[pred_idx])));

        pArrive[pred_idx] = 1.0 - pLeave[pred_idx] - autocorr[pred_idx];
    }

		string outputfilename = base_name;
        outputfilename += ".txt";

		outputfile.open(outputfilename.c_str());
        outputfile << "Random seed: " << seed << endl; // write seed to output file
		outputfile << "L1;" << pLeave[0] << endl;
		outputfile << "A1;" << pArrive[0] << endl;
		outputfile << "L2;" << pLeave[1] << endl;
		outputfile << "A2;" << pArrive[1] << endl;
		outputfile << "autocorr1;" << autocorr[0] << endl;
		outputfile << "autocorr2;" << autocorr[1] << endl;
		outputfile << "risk1;" << risk[0] << endl;
		outputfile << "risk2;" << risk[1] << endl;
		outputfile << "vanish_threshold;" << vanish_threshold << endl;
		outputfile << "alpha;" << alpha << endl;
		outputfile << "mu0;" << mu0 << endl;
		outputfile << "hmin;" << hmin << endl;
		outputfile << "maxD;" << maxD << endl;
		outputfile << "maxI;" << maxI << endl;
		outputfile << "maxT;" << maxT << endl;
		outputfile << "maxH;" << maxH << endl;
		outputfile << "K;" << K << endl;
		outputfile << "r;" << repair << endl;
		outputfile << "pAtt1;" << pAttack[0] << endl;
		outputfile << "pAtt2;" << pAttack[1] << endl;
        outputfile << "rep;" << replicate << endl;

        FinalFit();
        PredProb();
        
        for (unsigned t_idx{0}; t_idx <= maxT; ++t_idx)
        {
            std::cout << "pPred1_" << t_idx << ";";
            std::cout << "pPred2_" << t_idx << ";";
            std::cout << "pPred12_" << t_idx << ";";
        }

        std::cout << std::endl;

        for (unsigned t_idx{0}; t_idx <= maxT; ++t_idx)
        {
            std::cout << pPred[pred1][t_idx] << ";";
            std::cout << pPred[pred2][t_idx] << ";";
            std::cout << pPred[pred12][t_idx] << ";";
        }

        Predation();
        Mortality();
        Damage();
//        Reproduction();

        cout << "i" << "\t" << "totfitdiff" << endl;
        for (i=1;i<=maxI;i++)
          {
          OptDec();
          ReplaceFit();

          if (totfitdiff < 0.000001) break; // strategy has converged on optimal solution, so exit loop
          if (i==maxI) { outputfile << "*** DID NOT CONVERGE WITHIN " << i << " ITERATIONS ***" << endl;}

 		  if (i%skip==0)
            {
              cout << i << "\t" << totfitdiff << endl; // show fitness difference every 'skip' generations
            }
          }

        cout << endl;
        outputfile << endl;

        PrintStrat();
        PrintParams();
        outputfile.close();

        fwdCalc(base_name);
        SimAttacks(base_name);

  return 0;
}
