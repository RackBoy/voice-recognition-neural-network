#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "config.h"


void dct(double *d,double *c,int n){
  double angle;

  int i;
  int j;
  const double r8_pi = 3.141592653589793;

  for (i=0;i<n;i++){
    c[i] = 0.0;
    for(j=0;j<n;j++){
      angle=r8_pi*(double)(i*(2*j+1))/(double)(2*n);
      c[i]=c[i]+cos(angle)*d[j];
    }
    c[i]=c[i]*(i==0?1.0/sqrt((double )n):sqrt(2.0/(double)(n)));
  }

}

//this function seeks d max value of an array in abs & normalizes
void normalize(short *nums,double *output,int size){
  
  short top;
	top=abs(nums[0]);

	for(int i=1;i<size;++i){
		if(abs(nums[i])>top) 
      top=nums[i];
	}

  	for(int i=0;i<size;++i){
		output[i]=(double)nums[i]/(double)top;
	}
}

//this function makes the convolution of 2 arrays
void conv(double *x, double *h, double *y,int nx,int p){
    int i,j;

    for(i=0;i<(nx+p-1);i++){
        y[i]=0.0;
        for(j=0;j<p;j++){
           if(((i-j)>=0) && ((i-j)<nx))
           y[i]=y[i]+x[i-j]*h[j];
          }
      }
}

//function to copies numbers from an array to another
//destiny where numbers will be, source data and size of arrays (equal 4 both)
void copyNums(double *dest, double *src, int size){

  for(int i=0;i<size;i++)
      dest[i]=src[i];

}

void decimateBy2(double *x,double *h, double *a, int nx, int p){

  int size=(nx+p-1)/2;

  double pair[nx/2+(nx%2)],no_pair[nx/2];
	double h00[p/2];
	double h01[p/2];
	double ya0[size];
	double ya1[size];
	int x_pair=0,x_inpair=0; //aux to pos array

  double y1[size];
  double y2[size];

  for(int n=0;n<size;n++) //fills up y1 & y1 with zeros
    y1[n]=y2[n]=0;


	for(int i=0;i<nx;i++){ //splits pair & no pair values

			if(i%2==0){

        pair[x_pair]=x[i];
				x_pair++;
		}
		else {

      no_pair[x_inpair]=x[i];
			x_inpair++;
		}
	}

  x_inpair=x_pair=0;  //resets vars

  for(int i=0;i<p;i++){ //splits pair & no pair values from h0

			if(i%2==0){

				h00[x_pair]=h[i];
				x_pair++;
		}
		else {

			h01[x_inpair]=h[i];
			x_inpair++;
		}
	} // end for

  x_inpair=x_pair=0;  //resets vars

  conv(pair, h01, y1,nx/2+(nx%2),p/2);
  conv(no_pair, h00, y2,nx/2,p/2);

  for(int k=0;k<size;k++) //final result
    a[k]=y1[k]+y2[k];

} // end function


void dwt(double *x, double *h0,double *g0,double *a,double *d, int nx,int p){
decimateBy2(x,h0,a,nx,p);
decimateBy2(x,g0,d,nx,p);
}


// Multi-level Wavelet decomposition
void wavedec(
double *x, // Input signal
double *h0, // Impulse response of low-pass filter
double *g0, // Impulse response of high-pass filter
double **c, // Wavelet coefficients (pointer is allocated), its d result
int **levels, // Size for each level in c (pointer is allocated)
int nx, // Size of x
int p, // Size of impulse responses h0 and g0
int nl // Number of Wavelet levels

){
  int size=(nx+p-1)/2;
  int ndata=nx; //change array size in each iteration 4 d new dwt process
  double a[size];
  double d[size];
  double *aux_cc; //saves sizez of d dynamic memory
  int *aux_l;
  int n_total; //saves size of each array position
  int offset;

  // this calculates d sizes of the array called levels
  *levels=malloc((nl+2)*sizeof(int));
  aux_l=*levels;

  n_total=0;
  //this loop calculates sizes and levels: n_total and levels (aux_l)
   for(int k=0;k<nl;k++){
        n_total+=(ndata+p-1)/2;
        aux_l[nl-k]=(ndata+p-1)/2;  //levels here
        ndata=(ndata+p-1)/2;
  }

  aux_l[0]=aux_l[1];
  aux_l[nl+1]=nx; //last pos of levels
  n_total+=aux_l[0];

  *c=malloc(n_total*sizeof(double));

  aux_cc=*c;
  ndata=nx;
  offset=n_total-aux_l[nl];

for(int i=0;i<nl;i++){

    dwt(x,h0,g0,a,d,ndata,p);
    ndata=(ndata+p-1)/2;// changes size 4 dwt in d next iteration
    copyNums(aux_cc+offset,d,ndata); //saves result of each iteration
    copyNums(x,a,ndata);  //updates new values of x
    offset-=aux_l[nl-(i+1)];

    } //end 1 for
copyNums(aux_cc,a,aux_l[0]);

} // end wavedec function


//this function calculates energy
void wenergy(double *c, int *l, int nl, double **E){

  double *aux_e;
  int *aux_l,offset=0;

  *E=malloc((nl+1)*sizeof(double));
  aux_l=l;
  aux_e=*E;
  
  for(int i=0;i<nl+1;i++){ //moves along levels
    aux_e[i]=0.0;
    for(int j=0;j<aux_l[i];j++) //moves along size of each level
        aux_e[i]+=c[j+offset]*c[j+offset];
        offset+=aux_l[i];
    }
} //end function energy

void extract_wcc(
short *x,
int nx,
int nl, 
int nf, // n frames
int ns, // n shitft 
int nw, // n window
int p, 
double *window, // hamming
double *h0,
double *g0,
double *wccs
){

  double Ed[nl]; 
  double y[nw];
  double Ea;
  double Ca;
  double Cd;
  double Ce1;
  double Ce2;
  double Ce;
  double aux_x[nw];
  double aux_xd[nx];
  double x_prev=0;
  double aux_1=0;
  double aux_1_energy[nf]; //it saves d power
  double *c;
  int *levs;
  double *E;
  double aux_c[nl+1];
  double exp22=1e-22; //it prevents log 0 error

  normalize(x,aux_xd,nx); //calculates max value from x & normalizes d signal

  
//----------------- loops begin here ----------------
   
  for(int i=0;i<nf;i++){ // n frames, til 20

    aux_1=0.0;
    for(int k=(i*ns);k<nw+(i*ns);k++){    //n window. speech frame here. til 256

    //Ce1=x[k+i/2]*x[k+i/2]; 
      
    //each frame from x its splitted up here
      aux_1+=x[k]*x[k]; //energy
      aux_x[k-(i*ns)]=x[k]-0.95*x_prev*window[k-(i*ns)]; //hamin product
      x_prev=x[k];

  } // end for nw

  aux_1_energy[i]=aux_1; //this is 4 d energfy
    
    //if(aux_1_energy==0)
    if(aux_1_energy<0)
        Ce=log10(exp22);
      
    Ce=log10(aux_1_energy[i]);  //log op ici

    wavedec(aux_x,h0,g0,&c,&levs,nx,p,nl);
    wenergy(c,levs,nl,&E);

    for(int n=0;n<nl+1;n++)
      E[n]=log10(E[n]);

    //DCT ici
    dct(E,aux_c,nl);

    //copy on wcss d final result
    copyNums(&wccs[i*(nl+1)],aux_c,sizeof(nl+1));
    
      //aux_1=0;
    //for(int u=0;u<nw;u++){
      //y[u]=aux_x[u]-0.95*aux_1;
     // aux_1=aux_x[u];
    //}
        
    //hammin
      //for(int n=0;n<nw;n++) //n window 256
      
    }// end for nf
  
} //end function


int main(){

  double x[]={1,2,3,4,5,6,7,8};
  int nx=8;
  int nl=3;
  int size=(nx+P-1)/2;
  double *c;
  double *e;
  int *levels;

  double *aux_h0,*aux_g0;
  aux_h0=(double*)h0;
  aux_g0=(double*)g0;

  double res[size];
  double res1[size];

  wavedec(x,aux_h0,aux_g0,&c,&levels,nx,P,nl);
  wenergy(c,levels,nl,&e);

for(int l=0;l<15;l++){
    printf("Res c: %f",c[l]);
    printf("\n");
    }

  for(int j=0;j<5;j++){
    printf("Levels: %d",levels[j]);
    printf("\n");
  }

  for(int k=0;k<4;k++){
    printf("Energy: %f",e[k]);
    printf("\n");
  }

  return 0;
}
