/*SRC_files/SRC.c    
* Sarabjot Singh Khangura

SRC - A C/C++ application for encoding file using Simple Regenerating Code
Copright (C) 2010 Sarabjot Singh Khangura
    
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.

Sarabjot Singh Khangura
Electrical Engineering Department
University of Southern California
Los Angeles, CA 90007
email:skhangur@usc.edu,khangurasarabjot@gmail.com   


/**************************************************************************************
SRC program encodes input file using SRC. 
Usage:'SRC <name of the file to be encoded> <k> <n> <f> <field size> <buffersize>'. n, k, f are SRC code parameters.
This would generate 'n' encoded files using SRC and a metafile with all the details needed for repair and decoder applications.
For detail on SRC, refer to "Simple Regenerating Codes: Network Coding for Cloud Storage by D. S. Papailiopoulos, J. Luo, A. G. Dimakis, C. Huang, and J. Li "

***************************************************************************************/



#include <sys/time.h>
#include <sys/stat.h>
#include <string.h>
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <time.h>
#include <errno.h>	
#include "jerasure.h"
#include "reed_sol.h"
#include "galois.h"
#include "cauchy.h"



/* data structure for generating Lookup Table for the code*/

typedef struct {
	int chunkIndex; 
	long start;
	long Nbytes;
} chunkInfoType;

typedef struct {
	chunkInfoType chunkInfo;
} lookupTable;

lookupTable **LookupTable;
/* data structure ends*/



main(int argc, char **argv) {
	/* code parameters*/
	/* m = n-k */ 	
	int n,k,f,w,m;
					
	/* file pointer*/								
	FILE *fp;

	/* variables to store original size and new size after adjusting to make chunks integral multiple of buffersize*/
	int size, newsize;
	struct stat status;

	/* size of the buffer used to read the input file*/
	long buffersize;
		
	/*loop variables*/
	int i, j,q,a,z;
	
	/* variables to keep account of the data read from the file and written to files*/ 								
	int *total;
	int extra;
	
	/* Number of times a read system call is made for each chunk*/
	int readins;
		
	/*variable used to construct name of files*/
	char *fname;
	char *metafilename;
	char *s1, *s2;	
	char *curdir;
	
	/* used for storing name of the encoded files*/ 					
	char **nodes;
	
	/* File streams used to read from the input file*/
	FILE **readFileStreams;
	
	/*file stream for writting metafile that stores meta data*/
	FILE *meta;
	
	/* file stream for writting to the encoded files*/ 
	FILE **writeStreams;
	
	/* stores the size of a chunk in SRC*/
	int chunkSize = 0;
	
	/* encoding matrix*/
	int *matrix;	

	/* data,coding and xor buffers*/  
	char **data;
	char **coding;
	char **xor;

	/* temp variable for adjusting buffersize*/
	int up;
	int down;
	
	/* used in generating look up table*/
	int temp_map = 0;

	
	/* Timing variables */
	struct timeval t1,t2;
	struct timeval t3,t4;
	struct timezone tz;
	double totalsec,enc_time;
	double tsec;
	/*start the time*/
	/*totalsec is the time taken to complete the process*/
	/*enc_time is the total time taken to encode the file. It excludes I/O times*/   
	gettimeofday(&t1, &tz);
	totalsec = 0.0;
	enc_time = 0.0;

	if (argc != 7) {
			fprintf(stderr,  "usage: inputfile k n f w buffersize\n");
			exit(0);
		}
		/* Conversion of parameters and error checking */
		if (sscanf(argv[2], "%d", &k) == 0 || k <= 0) {
			fprintf(stderr,  "Invalid value for k\n");
			exit(0);
		}
		if (sscanf(argv[3], "%d", &n) == 0 || n < k) {
			fprintf(stderr,  "Invalid value for n\n");
			exit(0);
		}
		if (sscanf(argv[4], "%d", &f) == 0 ||(n<=f)) {
				fprintf(stderr,  "Invalid value for f\n");
				exit(0);
				}
		if (sscanf(argv[5],"%d", &w) == 0 || w <= 0) {
			fprintf(stderr,  "Invalid value for w.\n");
			exit(0);
		}
		
	if (argc != 7) {
			buffersize = 0;
		}
		else {
			if (sscanf(argv[6], "%ld", &buffersize) == 0 || buffersize <= 0) {
				fprintf(stderr, "Invalid value for buffersize\n");
				exit(0);
			}

		}
		
	// make a directory by the name coding
	/* Get current working directory for construction of file names */
	curdir = (char*)malloc(sizeof(char)*1000);
	getcwd(curdir, 1000);

	/* Open file and error check */
	fp = fopen(argv[1], "rb");
		if (fp == NULL) {
			fprintf(stderr,  "Unable to open file %s.\n",argv[1]);
			exit(0);
		}

	/* Create Coding directory */
	i = mkdir("Coding", S_IRWXU);
	if (i == -1 && errno != EEXIST) {
		fprintf(stderr, "Unable to create Coding directory.\n");
		exit(0);
		}

	stat(argv[1], &status);
	size = status.st_size;
	
	/* adjust buffersize */
	if (buffersize%(sizeof(int)*w) != 0) {
			up = buffersize;
			down = buffersize;
			while (up%(sizeof(int)*w) != 0 && down%(sizeof(int)*w) != 0) {
				up++;
				down--;
			}
			if (up%(sizeof(int)*w) == 0) {
				buffersize = up;
			}
			else {
				buffersize = down;
			}
		}

	newsize = size;


	/* find size of the chunks in SRC */ 
	chunkSize = newsize/(f*k);
	if (buffersize != 0) {
		while ((newsize%(k*f*w*sizeof(int)) != 0)||(chunkSize%buffersize !=0)||(newsize%(buffersize) != 0)) {
				newsize++;
				chunkSize = newsize/(f*k);
			}
	}
	
	
	

	/*assign data and coding buffers memory location*/
	m = n-k;
	data = (char**)malloc(sizeof(char*)*k);
	coding = (char**)malloc(sizeof(char*)*m);
	xor = (char**)malloc(sizeof(char*)*n);
	
	/*find the number of read system calls to be made to read a chunk in a memory*/
	if (chunkSize > buffersize && buffersize != 0) {
			if (chunkSize%buffersize != 0) {
				readins = chunkSize/buffersize;
			}
			else {

				readins = chunkSize/buffersize;
			}
			for(i=0;i<(k);i++)
				if((data[i] = (char *)malloc(sizeof(char)*buffersize))==NULL){
					printf("ERROR:Could not assign memory for data buffer %d\n",i);
					exit(0);
					}
			for(i=0;i<(m);i++)
				if((coding[i] = (char*)malloc(sizeof(char)*buffersize))==NULL){
					printf("Error:Could not assign memory for coding buffer\n",i);
					exit(0);
				
				}
			}
		else {
			readins = 1;
			buffersize = chunkSize;
			for(i=0;i<(k);i++)
				if((data[i] = (char *)malloc(sizeof(char)*buffersize))==NULL){
					printf("ERROR:Could not assign memory for data buffer %d\n",i);
					exit(0);
					}
			for(i=0;i<(m);i++)
				if((coding[i] = (char*)malloc(sizeof(char)*buffersize))==NULL){
					printf("Error:Could not assign memory for coding buffer\n",i);
					exit(0);
				
			}
		}


	/* create a look up table for placement of chunks into 'n' encoded files*/
	temp_map = 0;
	LookupTable = (lookupTable**)malloc(sizeof(lookupTable*)*(n)*(f+1));
	for(i=0;i<(n)*(f+1);i++)
		LookupTable[i] = (lookupTable*)malloc(sizeof(lookupTable));
		
	temp_map = n;
	for(i = 0; i<f+1; i++){
		for(j=0;(j<n);j++){
			(LookupTable[i+(f+1)*j]->chunkInfo).chunkIndex = (j+temp_map) % n;
			(LookupTable[i+(f+1)*j]->chunkInfo).Nbytes = chunkSize;
			(LookupTable[i+(f+1)*j]->chunkInfo).start = i*chunkSize;
			}
			temp_map--;
	}	
	temp_map = 0;
	
		
	/*Create read stream for input file*/
	if((readFileStreams = (FILE **)malloc(sizeof(FILE*)*k)) == NULL){
		printf("Error:Could not assign memory for file streams\n",i);
		exit(0);
	}
	
	if((nodes = (char **)malloc(sizeof(char*)*n)) == NULL){
		printf("Error:Could not assign memory for storing names of the encoded files\n",i);
		exit(0);
	}		
	if((writeStreams = (FILE**)malloc(sizeof(FILE*)*n))==NULL){
		printf("Error:Could not assign memory for write streams\n",i);
		exit(0);
	}

	
	s1 = (char*)malloc(sizeof(char)*(strlen(argv[1])+10));
		s2 = strrchr(argv[1], '/');
		if (s2 != NULL) {
			s2++;
			strcpy(s1, s2);
		}
		else {
			strcpy(s1, argv[1]);
		}
		s2 = strchr(s1, '.');
		if (s2 != NULL) {
			*s2 = '\0';
		}
		fname = strchr(argv[1], '.');
		s2 = (char*)malloc(sizeof(char)*(strlen(argv[1])+5));
		if (fname != NULL) {
			strcpy(s2, fname);
		}

		
		
		
		
		
		for(i = 0; i < n; i++){
			nodes[i] = (char*)malloc((sizeof(char)*(strlen(argv[1])+strlen(curdir)+strlen(s1)+20)));
			sprintf(nodes[i],"%s/Coding/%s_data_%d%s",curdir,s1,i,s2);
			}	
		
		total = (int*)malloc(sizeof(int)*f*k);
		
		
		
	
		
		// open write streams
		for(i=0;i<n;i++)
			writeStreams[i] = fopen(nodes[i],"wb");
		//end
		for(i=0;i<(f*k);i++)
			total[i] = 0;
		
		/* writting to meta file*/
		metafilename=(char*)malloc(sizeof(char)*1000);	
		sprintf(metafilename,"%s/Coding/%s_metanames.txt",curdir,s1);
		meta=fopen(metafilename,"wb");
		for(i=0;i<n;i++){
			fprintf(meta, "%s\n", nodes[i]);
			}
		fprintf(meta,"chunkSize = %d\n",chunkSize);
		fprintf(meta,"orignalsize = %d\n",size);
		fprintf(meta,"newsize = %d\n",newsize);
		fprintf(meta,"k = %d\n",k);
		fprintf(meta,"n = %d\n",n);
		fprintf(meta,"w = %d\n",w);
		fprintf(meta,"f = %d\n",f);
		fprintf(meta,"buffersize = %ld\n",buffersize);
		fclose(meta);	
		free(metafilename);
				
	/*vandermonde matrix for coding*/
	matrix = reed_sol_vandermonde_coding_matrix(k, m, w);
	for(j=0;j<(k);j++)
		if((readFileStreams[j] = fopen(argv[1],"rb")) == NULL){
			printf("Could not open file to read\n");
		}
		
	
	/* reading from the file*/
	z=1;
	while (z <= readins) {	
	
		/*reassigning memory for buffers to store xors of coded streams*/
		for(j=0;j<n;j++)
				if((xor[j] = (char*)calloc(buffersize,sizeof(char)))==NULL){
					printf("Low memory\n");
					exit(0);
					}
		/*seeking readstream stream*/
		/*we read data equal to buffersize from the start of each chunk*/
		for(i=0;i<f;i++){
			for(j=0;j<k;j++){
					fseek(readFileStreams[j],(j+i*(k))*chunkSize+(z-1)*buffersize,SEEK_SET);
				}	
			// reading k stream to code them using vandermonde matrix 
				for(j=0;j<k;j++){	   
						if (total[j+k*i] < chunkSize && total[j+k*i]+buffersize <= chunkSize) {
							total[j+k*i] += fread(data[j], sizeof(char), buffersize, readFileStreams[j]);
							fflush(readFileStreams[j]);
						}
						else if (total[j+k*i] < chunkSize && total[j+k*i]+buffersize > chunkSize) {
							extra = fread(data[j], sizeof(char), buffersize, readFileStreams[j]);
							fflush(readFileStreams[j]);
							for (q = extra; q < buffersize; q++) {
								data[j][q] = '0';
							}
						}
						else if (total[j+k*i] == chunkSize) {
							for (q = 0; q < buffersize; q++) {
								data[j][q] = '0';
							}
						}
					}
			/*encoding data streams */
			gettimeofday(&t3, &tz);	
			jerasure_matrix_encode(k, m, w, matrix, data,coding, buffersize); 
				
			
			/*xor streams before writting them to file*/
			/*xor buffer accumulates xors of the streams, once we xor 'f' buffers, it is written to file*/
			for(j=0;j<k;j++)
					galois_region_xor(xor[j],data[j],xor[j],buffersize);
			for(j=0;j<m;j++)		
					galois_region_xor(xor[j+k],coding[j],xor[j+k],buffersize);
			
			gettimeofday(&t4, &tz);
			tsec = 0.0;
			tsec += t4.tv_usec;
			tsec -= t3.tv_usec;
			tsec /= 1000000.0;
			tsec += t4.tv_sec;
			tsec -= t3.tv_sec;
			enc_time += tsec; 		
			
			/*seek file position to write data and coding buffers*/
			for(j = 0;j < n;j++){
				fseek(writeStreams[j],((z-1)*buffersize+i*chunkSize),SEEK_SET);
				}
			/*writting buffers to designated places using look up table*/	
			for(j = 0;j < n;j++){
				
				if(((LookupTable[i+(f+1)*j]->chunkInfo).chunkIndex) < k){
					if (writeStreams[j] == NULL) {
						printf("Could not Write data buffer to file\n");
						exit(0);
					} else {
						fwrite(data[(LookupTable[i+(f+1)*j]->chunkInfo).chunkIndex], sizeof(char), buffersize, writeStreams[j]);
						fflush(writeStreams[j]);
					}
				}
			
				else{
					if (writeStreams[j] == NULL) {
						printf("Could not Write coding buffer to file\n");
						exit(0);
					} else {
						fwrite(coding[(LookupTable[i+(f+1)*j]->chunkInfo).chunkIndex - k], sizeof(char), buffersize, writeStreams[j]);
						fflush(writeStreams[j]);
					}
				}		
			}			
		}	
		
		/*write xors to their designated places*/
		for(j=0;j<(n);j++){
			if (writeStreams[j] == NULL) {
					printf("Could not Write data buffer to file\n");
					exit(0);
			} else {
				fseek(writeStreams[j],((z-1)*buffersize)+i*chunkSize,SEEK_SET); 
				fwrite(xor[(LookupTable[i+(f+1)*j]->chunkInfo).chunkIndex], sizeof(char), buffersize, writeStreams[j]);
				fflush(writeStreams[j]);
			}
		}		
		/*free buffer as they will reassigned memory*/						
		for(j=0;j<n;j++)	
			free(xor[j]);
		z++;
		}
		/*free data and coding buffers */
		for(i=0;i<(k);i++)
			free(data[i]);	
		for(i=0;i<(m);i++)
			free(coding[i]);
			
			
		// measuring time
		gettimeofday(&t2, &tz);
		tsec = 0.0;
		tsec += t2.tv_usec;
		tsec -= t1.tv_usec;
		tsec /= 1000000.0;
		tsec += t2.tv_sec;
		tsec -= t1.tv_sec;
		totalsec += tsec;
		//Calculating Encoding rate
		printf("Time taken to encode file of size %d is %0.10f\n",size,enc_time);
		printf("Encoding Rate (size of file/total time) is %0.10f\n",(((float)size/1024)/1024)/(enc_time));
			
	
	return 0;
}
		
