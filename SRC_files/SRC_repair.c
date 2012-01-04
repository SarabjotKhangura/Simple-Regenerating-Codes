/*SRC_files/SRC_repair.c    
* Sarabjot Singh Khangura

SRC - A C/C++ application for reparing storage system that uses Simple Regenerating Code
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
This program repairs SRC system when upto (n-k) encoded files are lost.
   It has two specialized repair functions:
   a. Repair function when we lose only one encoded file storing the data. It uses xor function from jerasure library to Recover erased encoded file.   
   b. Recover function which is used when lose more than one but upto (n-k) encoded files. It uses decoding function from jerasure libaray as well 
      as xor function.	
   Usage:'SRC_repair <name of the file that was encoded using SRC>'
For detail on SRC, refer to "Simple Regenerating Codes: Network Coding for Cloud Storage by D. S. Papailiopoulos, J. Luo, A. G. Dimakis, C. Huang, and J. Li "

***************************************************************************************/





#include <sys/time.h>
#include <sys/stat.h>
#include <string.h>
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <errno.h>
#include <signal.h>
#include <time.h>
#include "jerasure.h"
#include "reed_sol.h"
#include "galois.h"
#include "cauchy.h"
#include "liberation.h"

/*file pointer for metafile*/
FILE *meta;

/*array of file pointers for reading from fles*/
FILE **filestreams;
FILE **ReadFileStreams;

/*variable to keep account of files lost*/
int filesUnavailable = 0;
char **fileNamesUnavailable;
int *nodeIndexUnavailable;

/* code parameters*/
int n,k,f,w,m =0;
int buffersize = 0;                          	
long chunkSize = 0;

/*strings used for reading metafile*/						
char *String;							
char **file2beread;


int readins;
int size = 0;

/*encoding matrix for reed solomon encoder*/
int *encoder_matrix;

/*file pointers for files in repair*/
FILE **filesInRepair;

/*file used for repairng SRC system*/
int *files2ReadFrom;


typedef struct {
int fileIndex; 
long start;
long Nbytes;
} chunkInfoType;

typedef struct {
chunkInfoType chunkInfo;
} lookupTable;

/*creating look up table*/
lookupTable **LookupTable;

/*look up tables storing information about chunks lost because of erasures*/
lookupTable *nodePacketData;
lookupTable *repairChunksTable;


/*used in jerasure decode functiosn*/
int *erasure;
int *erasedstream;
int *erasedArray;

/*buffers used to xor data*/
char **xorBuffer;
char *xorResultBuffer;


void Recover()
{
	
	/*loop variables*/
	int i,j,p,temp,q,offset;
	
	int readcheck,extra,readin,writecheck;
	
	FILE **packetStreams;							
	char *filename;
	int newsize,up,down,readins;
	
	int *total;
	
	int filesSurviving;
	int *erasedFiles;
	int fileserased;
	char **data,**coding;
	char **blockBuffer;
	int m;
	int index;
	int decodeFlag;
	int e,z;                                					//loop variable
	
	
	struct timeval t1,t2;
	struct timezone tz;
	double totalsec,tsec;
	struct timeval start, stop;
	
	// starting the timer
	totalsec = 0.0;
	

	m = n-k;
	encoder_matrix = NULL;

	/*encoding matrix for reed solomon coding*/
	encoder_matrix = reed_sol_vandermonde_coding_matrix(k, m, w);

	
	total = (int*)malloc(sizeof(int)*n);		
	
	repairChunksTable = (lookupTable *)malloc(sizeof(lookupTable)*(f)*(f+1));
	data = (char**)malloc(sizeof(char*)*k);
	coding = (char**)malloc(sizeof(char*)*m);	
		
	nodePacketData = (lookupTable*)malloc(sizeof(lookupTable)*(f+1)*k);
	repairChunksTable = (lookupTable*)malloc(sizeof(lookupTable)*(f)*filesUnavailable);	
	
	filesInRepair = (FILE**)malloc(sizeof(FILE*)*(filesUnavailable));				
			
	/*printf("Lost Files are :\n");	
	for(i=0;i<filesUnavailable;i++)
		printf("%d. %s\n",i,fileNamesUnavailable[i]);
	*/
	
	
	files2ReadFrom = (int*)malloc(sizeof(int)*(k));
	erasedFiles = (int*)malloc(sizeof(int)*filesUnavailable);
	erasure = (int*)malloc(sizeof(int)*(n-k+1));
	erasedstream = (int*)malloc(sizeof(int)*(n-k+1));
	erasedArray = 	(int*)malloc(sizeof(int)*(n));
	
	/*initialize array storing the indices of the files lost*/
	for(i=0;i<n;i++)
		erasedArray[i] = -1;
	
	j=0;
	for(i=0;i<n;i++){
		if((nodeIndexUnavailable[i] == 1)){
			erasedFiles[j] = i;
			j++;	
		}
	}
	// -1 indicates available and 1 indicates lost	
	
	// pick any k files to read from surviving files and assume other files erasures 
	j=0;
	p=0;
	for(i=0;i<n;i++){
		if((nodeIndexUnavailable[i] == -1)&&(j<k)){
			files2ReadFrom[j] = i;
			j++;	
		}
		else{
			erasure[p] = i;
			erasedstream[p] = i;
			p++;
		}
	}
	
	/*download info for the chunks in surviving files*/
	erasure[p] = -1;
	erasedstream[p] = -1; 
	j=0;
	filesSurviving = 0;
	for(j=0;j<k;j++){
		for(i = filesSurviving;i<n;i++){
			if(nodeIndexUnavailable[i] == -1){
				filesSurviving = i;
				break;
			}
		}		
	 
		for(i=0;i<(f+1);i++){
			(nodePacketData[i + j*(f+1)].chunkInfo).fileIndex = ((LookupTable[i+filesSurviving*(f+1)])->chunkInfo).fileIndex;
			(nodePacketData[i+ j*(f+1)].chunkInfo).start = ((LookupTable[i+filesSurviving*(f+1)])->chunkInfo).start;		
			((nodePacketData[i + j*(f+1)].chunkInfo).Nbytes =((LookupTable[i+filesSurviving*(f+1)])->chunkInfo).Nbytes);
		}
		filesSurviving = filesSurviving + 1;		
	}
	
		

	/* determine number of read-ins */
	if (chunkSize > buffersize && buffersize != 0) {
		if (chunkSize%buffersize != 0) {
			readins = chunkSize/buffersize;
		}
		else {
			readins = chunkSize/buffersize;
		}
		}
	else {
		readins = 1;
		buffersize = chunkSize;
	}	
	// Pick any k Healthy nodes..... to read data from....
	
	
	for(i=0;i<filesUnavailable;i++)
		if((filesInRepair[i] = fopen(fileNamesUnavailable[i],"ab")) == NULL)
			printf("File Could not be Created for replacing failed node\n");
	
				
	
	//open files to read from
	ReadFileStreams = (FILE**)malloc(sizeof(FILE*)*k);
	for(i=0;i<k;i++)
		if((ReadFileStreams[i] = fopen(file2beread[files2ReadFrom[i]],"rb")) == NULL)		
			printf("Unable to read file \n");
			
			
	/*assign memory for data and coding buffers*/
	for(i=0;i<f;i++){
		for(j=0;j<k;j++){
			if(readins == 1)
				data[j] = (char*)calloc(chunkSize,sizeof(char));
			else
				data[j] = (char*)calloc(buffersize,sizeof(char));	
		}
		for(j=0;j<m;j++){
			if(readins == 1)
				coding[j] = (char*)calloc(chunkSize,sizeof(char));
			else
				coding[j] = (char*)calloc(buffersize,sizeof(char));	
		}
		for(j=0;j<n;j++)
			total[j] = 0;
		
	
		p=1;
		while(p<=readins){
			for(j=0;j<k;j++){
				fseek(ReadFileStreams[j],i*chunkSize+(p-1)*buffersize,SEEK_SET);
						
				/*read from files into buffer*/
				/*if chunk's fileindex is less than k, read it into data buffer
				if chunk's fileindex is greater than k, read it into coding buffer*/
				if((nodePacketData[i + j*(f+1)].chunkInfo).fileIndex < k){
					index = (nodePacketData[i + j*(f+1)].chunkInfo).fileIndex;
					erasedArray[index] = 1;
					if (total[index] < chunkSize && total[index]+buffersize <= chunkSize) {
							total[index] += fread(data[index], sizeof(char), buffersize,ReadFileStreams[j]);
							fflush(ReadFileStreams[j]);
						}
						else if (total[index] < chunkSize && total[index]+buffersize > chunkSize) {
							extra = fread(data[index], sizeof(char), buffersize, ReadFileStreams[j]);
							fflush(ReadFileStreams[j]);
							for (q = extra; q < buffersize; q++) {
								data[index][q] = '0';
							}
						}
						else if (total[index] == chunkSize) {
							for (q = 0; q < buffersize; q++) {
								data[index][q] = '0';
							}
						}
				
					}
				else{
					index = (nodePacketData[i + j*(f+1)].chunkInfo).fileIndex-k;
					erasedArray[index+k] = 1;
					if (total[index+k] < chunkSize && total[index+k]+buffersize <= chunkSize) {
							total[index+k] += fread(coding[index], sizeof(char), buffersize,ReadFileStreams[j]);
							fflush(ReadFileStreams[j]);
						}
						else if (total[index+k] < chunkSize && total[index+k]+buffersize > chunkSize) {
							extra = fread(coding[index], sizeof(char), buffersize, ReadFileStreams[j]);
							fflush(ReadFileStreams[j]);
							for (q = extra; q < buffersize; q++) {
								coding[index][q] = '0';
							}
						}
						else if (total[index+k] == chunkSize) {
							for (q = 0; q < buffersize; q++) {
								coding[index][q] = '0';
							}
						}
				}
			}
			
			/*find out which buffers were filled and which were left empty, mark empty as erased*/
			z=0;
			for(j=0;j<n;j++){
				if(erasedArray[j] == -1){
					erasedstream[z] = j;
					z++;
				}
			}
			erasedstream[z] = -1;
			z = 0;
			gettimeofday(&t1, &tz);
			// pass coding and data buffers to decode function	
			if((decodeFlag = jerasure_matrix_decode(k, m, w, encoder_matrix, 1, erasedstream, data, coding, buffersize))==-1){
				printf("Decoding Failed\n");
				exit(0);
			}
			gettimeofday(&t2, &tz);
			tsec = 0.0;
			tsec += t2.tv_usec;
			tsec -= t1.tv_usec;
			tsec /= 1000000.0;
			tsec += t2.tv_sec;
			tsec -= t1.tv_sec;
			totalsec += tsec;
			
			
			for(j=0;j<n;j++)
				erasedArray[j] = -1;
			
			//  write recovered data to the new nodes 	
			for(j=0;j<filesUnavailable;j++){
				/* if index is greater less than k, it was data buffer that was lost
				if index is greater than k, it was coding buffer that was lost*/
				if((LookupTable[erasedFiles[j]*(f+1)+i]->chunkInfo).fileIndex < k){		
					index = (LookupTable[erasedFiles[j]*(f+1)+i]->chunkInfo).fileIndex;
					if (total[index] < chunkSize && total[index]+buffersize <= chunkSize) {
							total[index] += fwrite(data[index], sizeof(char), buffersize,filesInRepair[j]);
							fflush(filesInRepair[j]);
						}
						else if (total[index] < chunkSize && total[index]+buffersize > chunkSize) {
							extra = fwrite(data[index], sizeof(char), buffersize, filesInRepair[j]);
							fflush(filesInRepair[j]);
							for (q = extra; q < buffersize; q++) {
								data[index][q] = '0';
							}
						}
						else if (total[index] == chunkSize) {
							for (q = 0; q < buffersize; q++) {
								data[index][q] = '0';
							}
						}
				
					}
				else{
					index = (LookupTable[erasedFiles[j]*(f+1)+i]->chunkInfo).fileIndex-k;
					if (total[index+k] < chunkSize && total[index+k]+buffersize <= chunkSize) {
							total[index+k] += fwrite(coding[index], sizeof(char), buffersize,filesInRepair[j]);
							fflush(filesInRepair[j]);
						}
						else if (total[index+k] < chunkSize && total[index+k]+buffersize > chunkSize) {
							extra = fwrite(coding[index], sizeof(char), buffersize, filesInRepair[j]);
							fflush(filesInRepair[j]);
							for (q = extra; q < buffersize; q++) {
								coding[index][q] = '0';
							}
						}
						else if (total[index+k] == chunkSize) {
							for (q = 0; q < buffersize; q++) {
								coding[index][q] = '0';
							}
						}
				}		
			}
			p++;
		}
		/*free buffers*/
		for(j=0;j<k;j++)
			free(data[j]);
		for(j=0;j<m;j++)	
			free(coding[j]);	
	}
	
	/*close readstreams*/
	for(i=0;i<k;i++){
		fclose(ReadFileStreams[i]);
	}	
	/*last chunks in the lost files must have been xor of some other chunks in other files*/
	/*find their location, load them into buffer and xor them*/
	blockBuffer = (char**)malloc(sizeof(char*)*f);
	packetStreams = (FILE**)malloc(sizeof(FILE*)*f);
	for(i=0;i<f;i++){
		if(readins == 1)
			blockBuffer[i] = (char*)malloc(sizeof(char)*chunkSize);
		else
			blockBuffer[i] = (char*)malloc(sizeof(char)*buffersize);	
	}

	// using nodePacketData for failed nodes
	free(nodePacketData);
	nodePacketData = (lookupTable*)malloc(sizeof(lookupTable)*(1)*filesUnavailable);
	
	/*find location of chunks to xor from lookup table*/
	j=0;
	fileserased = 0;
	for(j=0;j<filesUnavailable;j++){
		for(i = fileserased;i<n;i++){
			if(nodeIndexUnavailable[i] == 1){
				fileserased = i;
				break;
			}
		}		
	 
			(nodePacketData[j].chunkInfo).fileIndex = ((LookupTable[(f)+fileserased*(f+1)])->chunkInfo).fileIndex;	
			(nodePacketData[j].chunkInfo).start = ((LookupTable[(f)+fileserased*(f+1)])->chunkInfo).start;		
			((nodePacketData[j].chunkInfo).Nbytes =((LookupTable[(f)+fileserased*(f+1)])->chunkInfo).Nbytes);
			fileserased = fileserased + 1;		
	}
	
	
		
	/*find the chunks to be xorred*/	
	temp = 0;
	for(e=0;e<filesUnavailable;e++,temp = 0){
		for(i=0;i<f;i++){
			for(j=0;j<n;j++){
					if(j==erasedFiles[e])
						continue;
					else{
						if(((nodePacketData[e]).chunkInfo).fileIndex == (LookupTable[i+(f+1)*j]->chunkInfo).fileIndex){
							((repairChunksTable[f*e+temp]).chunkInfo).fileIndex = j;		
							((repairChunksTable[f*e+temp]).chunkInfo).start = ((LookupTable[i+j*(f+1)])->chunkInfo).start;					
							((repairChunksTable[f*e+temp]).chunkInfo).Nbytes =((LookupTable[i+j*(f+1)])->chunkInfo).Nbytes;
							temp++;		
							}	
					}
				}
		}
	}	
	temp = 0;
	
	// xor the chunks read from the file
	
	for(q=0;q<filesUnavailable;q++){
			for(i=0;i<f;i++){
				packetStreams[i]=fopen(file2beread[((repairChunksTable[q*f+i]).chunkInfo).fileIndex],"rb");
				offset = (((repairChunksTable[q*f+i]).chunkInfo).start);
				if(fseek(packetStreams[i],(long)offset,SEEK_SET))
					printf("Unable to set file pointer");
				}
				
			for(i=0;i<f;i++)
				total[i] = 0;
			j=1;
			while(j<=readins){
				for(i=0;i<f;i++){	
					if (total[i] < chunkSize && total[i]+buffersize <= chunkSize) {
						total[i] += (readcheck=fread(blockBuffer[i], sizeof(char), buffersize, packetStreams[i]));
						}
												
										
				else if (total[i] < chunkSize && total[i]+buffersize > chunkSize) {
					total[i] += (readcheck=fread(blockBuffer[i], sizeof(char), buffersize, packetStreams[i]));
						for ( q = extra; q < buffersize; q++) {
							blockBuffer[i][q] = '0';
							}
					}
				else if (total[i] == chunkSize) {
					for ( q = 0; q < buffersize; q++) {
						blockBuffer[i][q] = '0';
								}
						}
					}
				j++;

				if(readins == 1)
					xorResultBuffer = (char*)calloc(chunkSize,sizeof(char));
				else
					xorResultBuffer = (char*)calloc(buffersize,sizeof(char));
				
				gettimeofday(&t1, &tz);		
				for(i=0;i<f;i++){
						galois_region_xor(xorResultBuffer,blockBuffer[i],xorResultBuffer,buffersize);
						}
				gettimeofday(&t2, &tz);
				tsec = 0.0;
				tsec += t2.tv_usec;
				tsec -= t1.tv_usec;
				tsec /= 1000000.0;
				tsec += t2.tv_sec;
				tsec -= t1.tv_sec;
				totalsec += tsec;		

				/*write xorred chunk to the file*/
				writecheck=fwrite((void*)xorResultBuffer, sizeof(char), buffersize,filesInRepair[q]);
				fflush(filesInRepair[q]);
				free(xorResultBuffer);
			}
			for(i=0;i<f;i++)
				fclose(packetStreams[i]);
		}
	  for(i=0;i<f;i++)
	  	free(blockBuffer[i]);
	  	
	
	//Calculating Encoding rate
	printf("Repair Rate when more than one node fails (total size of failed nodes/totaltime) is %0.10f\n",((((float)chunkSize*(f+1)*(filesUnavailable))/1024)/1024)/(totalsec));	
}


void Repair()
{
		
	int fileserased;
	int i,j,temp,q,offset;						
	int readcheck,extra,writecheck;
	int **packetsLost;
	FILE **packetStreams;							
	char *filename;
	int up,down;
	int *total;
		
	char **blockBuffer;
	struct timeval t1,t2;
	struct timezone tz;
	double totalsec,tsec;
	struct timeval start, stop;
	
	// starting the timer
	gettimeofday(&t1, &tz);
	totalsec = 0.0;
	
	packetsLost = (int**)malloc(sizeof(int*)*(f+1));
	for(i=0;i<(f+1);i++)
		packetsLost[i] = (int*)malloc(sizeof(int));			// assume f+1 is always for xor packets
	
	packetStreams = (FILE**)malloc(sizeof(FILE*)*(f));
	for(i=0;i<(f);i++)
		packetStreams[i] = (FILE*)malloc(sizeof(FILE));
		
	repairChunksTable = (lookupTable *)malloc(sizeof(lookupTable)*(f)*(f+1));
		
		
	nodePacketData = (lookupTable*)malloc(sizeof(lookupTable)*(f+1));	
	
	filesInRepair = (FILE**)malloc(sizeof(FILE*));				// no need for this but was giving segfault without it
	filesInRepair[0] = (FILE*)malloc(sizeof(FILE));
	

	filename = fileNamesUnavailable[0];
	
	
	// find which node failed	
	for(i=0;i<n;i++)					// this function can only recover one node from a failure
		if(nodeIndexUnavailable[i]==1)
			fileserased = i;	
	// end search
	
	// copying data of failed node
	for(i=0;i<(f+1);i++){
		(nodePacketData[i].chunkInfo).fileIndex = ((LookupTable[i+fileserased*(f+1)])->chunkInfo).fileIndex;
		(nodePacketData[i].chunkInfo).start = ((LookupTable[i+fileserased*(f+1)])->chunkInfo).start;		// assume last one to be xor packet
		((nodePacketData[i].chunkInfo).Nbytes =((LookupTable[i+fileserased*(f+1)])->chunkInfo).Nbytes);
		
		}
	
	
	// end copying
	
	
	
	
	/* Allow for buffersize and determine number of read-ins */
	if (chunkSize > buffersize && buffersize != 0) {
		if (chunkSize%buffersize != 0) {
			readins = chunkSize/buffersize;
		}
		else {
			readins = chunkSize/buffersize;
		}
		
		blockBuffer = (char**)malloc(sizeof(char*)*f);
		for(i=0;i<f;i++)
			blockBuffer[i] = (char*)malloc(sizeof(char)*buffersize);
		}
	else {
		readins = 1;
		buffersize = chunkSize;
		blockBuffer = (char**)malloc(sizeof(char*)*f);
		for(i=0;i<f;i++)
			blockBuffer[i] = (char*)malloc(sizeof(char)*chunkSize);
	}
	

	// find location of chunks to be xorred
	temp = 0;
	for(q=0;q<(f+1);q++,temp = 0){
		for(i=0;i<(f+1);i++){
			if(i==q)
				continue;
			else{	
				for(j=0;j<n;j++){
					if(j==fileserased)
						continue;
					else{
						if(((nodePacketData[q]).chunkInfo).fileIndex == (LookupTable[i+(f+1)*j]->chunkInfo).fileIndex){
							((repairChunksTable[f*q+temp]).chunkInfo).fileIndex = j;		
							((repairChunksTable[f*q+temp]).chunkInfo).start = ((LookupTable[i+j*(f+1)])->chunkInfo).start;					
							((repairChunksTable[f*q+temp]).chunkInfo).Nbytes =((LookupTable[i+j*(f+1)])->chunkInfo).Nbytes;
							temp++;		
							}		
					}	
				}
			}
	
		}
	
	}
	temp = 0;	
	
	/*open file stream to write*/	
	if((filesInRepair[0] = fopen(filename,"ab")) == NULL)
		printf("File Could not be Created for replacing failed node\n");
	
	
	total = (int *)malloc(sizeof(int)*f);
	
	for(q=0;q<f+1;q++){
			for(i=0;i<f;i++){
				packetStreams[i]=fopen(file2beread[((repairChunksTable[q*f+i]).chunkInfo).fileIndex],"rb");
				offset = (((repairChunksTable[q*f+i]).chunkInfo).start);
				if(fseek(packetStreams[i],(long)offset,SEEK_SET))
					printf("Unable to set file pointer");
				}
				
			for(i=0;i<f;i++)
				total[i] = 0;
			j=1;
			while(j<=readins){
				for(i=0;i<f;i++){	
					if (total[i] < chunkSize && total[i]+buffersize <= chunkSize) {
						total[i] += (readcheck=fread(blockBuffer[i], sizeof(char), buffersize, packetStreams[i]));
						}
												
										
				else if (total[i] < chunkSize && total[i]+buffersize > chunkSize) {
					total[i] += (readcheck=fread(blockBuffer[i], sizeof(char), buffersize, packetStreams[i]));
						for ( q = extra; q < buffersize; q++) {
							blockBuffer[i][q] = '0';
								}
						}
				else if (total[i] == chunkSize) {
					for ( q = 0; q < buffersize; q++) {
					blockBuffer[i][q] = '0';
							}
						}
					}
				j++;

				/*xor chunks read from the file*/
				if(readins == 1)
					xorResultBuffer = (char*)calloc(chunkSize,sizeof(char));
				else
					xorResultBuffer = (char*)calloc(buffersize,sizeof(char));
				gettimeofday(&t1, &tz);		
				for(i=0;i<f;i++){
						galois_region_xor(xorResultBuffer,blockBuffer[i],xorResultBuffer,buffersize);
						}
				gettimeofday(&t2, &tz);
				tsec = 0.0;
				tsec += t2.tv_usec;
				tsec -= t1.tv_usec;
				tsec /= 1000000.0;
				tsec += t2.tv_sec;
				tsec -= t1.tv_sec;
				totalsec += tsec;		

				/*write buffer to the file*/
				writecheck=fwrite((void*)xorResultBuffer, sizeof(char), buffersize,filesInRepair[0]);
				fflush(filesInRepair[0]);
				free(xorResultBuffer);
			}
		/*close the streams */
		for(i=0;i<f;i++)
			fclose(packetStreams[i]);
		}
	  /*free buffer memory*/		
	for(i=0;i<f;i++)
		free(blockBuffer[i]); 	
        fclose(filesInRepair[0]);            
	printf("Repair Rate (size of file/totaltime) is %0.10f\n",(((float)chunkSize*(f+1)/1024)/1024)/(totalsec));
	
	
return;	
	
}





int main(int argc, char **argv) 
{
	char *fname,*s1,*s2,*curdir;
	char *metafilename;
	

	int i,j,temp;
	char *searchstring,*tempstr,*line;

	if (argc != 2) {
		fprintf(stderr,  "usage: inputfile\n");
		exit(0);
		}
		
	/*find working directory*/	
	curdir = (char*)malloc(sizeof(char)*1000);
		getcwd(curdir,1000);
	
	fname = (char*)malloc((sizeof(char)*(strlen(argv[1])+strlen(curdir)+10)));	
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

	/*open metafile and read names of the encoded files,chunksize,code parameters,buffersize..etc*/
	metafilename=(char*)malloc(sizeof(char)*(strlen(argv[1])+strlen("Coding")+strlen(s1)+strlen("_metanames.txt")+10+strlen(curdir)));
	sprintf(metafilename,"%s/Coding/%s_metanames.txt",curdir,s1);
	if((meta = fopen(metafilename,"r"))==NULL){
		printf("No Meta file Present\n");
		exit(0);
	}
		

	line = (char*)malloc(sizeof(char)*500);
	tempstr = (char*)malloc(sizeof(char)*50);
	searchstring= (char*)malloc(sizeof(char)*500);
	String = (char*)malloc(sizeof(char)*20);
		
	
	temp = 0;
	i=0;
	j=0;
	
	while ((fgets (line,500, meta))!=NULL ) {
			char *p;
			sprintf(tempstr,"data_%d%s",j,s2);

			sprintf(searchstring,line); 
			p=strstr(searchstring,"\n");
			if(p!=NULL)
			*p = '\0';
			if((strstr(searchstring,"chunkSize =")!=NULL)&&(p=strstr(searchstring,"="))!=NULL)
			{
				strcpy(String,++p);			
				chunkSize = atol(String);
			}
			else if((strstr(searchstring,"orignalsize =")!=NULL)&&(p=strstr(searchstring,"="))!=NULL)
			{
				strcpy(String,++p);			
				size = atol(String);
			}
			else if((strstr(searchstring,"k =")!=NULL)&&(p=strstr(searchstring,"="))!=NULL)
			{
				strcpy(String,++p);			
				k = atol(String);
			}
			else if((strstr(searchstring,"n =")!=NULL)&&(p=strstr(searchstring,"="))!=NULL)
			{
				strcpy(String,++p);			
				n = atol(String);
			}
			else if((strstr(searchstring,"f =")!=NULL)&&(p=strstr(searchstring,"="))!=NULL)
			{
				strcpy(String,++p);			
				f = atol(String);
			}
			else if((strstr(searchstring,"buffersize =")!=NULL)&&(p=strstr(searchstring,"="))!=NULL)
			{
				strcpy(String,++p);			
				buffersize = atol(String);
			}
			else if((strstr(searchstring,"w =")!=NULL)&&(p=strstr(searchstring,"="))!=NULL)
			{
				strcpy(String,++p);			
				w = atol(String);
			}
			
							
		}
	fseek(meta, 0 ,SEEK_SET);
	filestreams = (FILE **)malloc(sizeof(FILE *)*n);
	file2beread = (char **)malloc(sizeof(char*)*n);
	nodeIndexUnavailable = (int *)malloc(sizeof(int)*n);
			
	/*fi*/
	temp = 0;
	for(i=0;i<n;i++){
		while ((fgets (line,500, meta))!=NULL ) {
			char *p;
			sprintf(tempstr,"data_%d%s",i,s2);

			sprintf(searchstring,line); /* write the line */
			p=strstr(searchstring,"\n");
			if(p!=NULL)
			*p = '\0';
			if((strstr(searchstring,tempstr)!=NULL)&&(strstr(searchstring,"=")==NULL))
			{
				file2beread[i] = (char *)malloc(sizeof(char)*strlen(searchstring));
				strcpy(file2beread[i],searchstring);		
				
			}
		
							
		}
		fseek(meta, 0 ,SEEK_SET);
	}
	fclose(meta);
	temp = 0;
	fileNamesUnavailable = (char **)malloc(sizeof(char*)*n);
	
	/*find files that were erased*/
	for(i=0;i<n;i++){
		if((filestreams[i] = fopen(file2beread[i],"rb")) == NULL){			
			filesUnavailable++;
			nodeIndexUnavailable[i] = 1;
			fileNamesUnavailable[filesUnavailable-1] = file2beread[i];
		}
		else {
			fclose(filestreams[i]);
			nodeIndexUnavailable[i] = -1;
		}	
	}	
	
	temp = 0;
	LookupTable = (lookupTable**)malloc(sizeof(lookupTable*)*(n)*(f+1));
	for(i=0;i<(n)*(f+1);i++)
		LookupTable[i] = (lookupTable*)malloc(sizeof(lookupTable));
	
	
	
	// create look up table 
	temp = n;
	for(i = 0; i<f+1; i++){
		for(j=0;(j<n);j++){
			(LookupTable[i+(f+1)*j]->chunkInfo).fileIndex = (j+temp) % n;
			(LookupTable[i+(f+1)*j]->chunkInfo).Nbytes = chunkSize;
			(LookupTable[i+(f+1)*j]->chunkInfo).start = i*chunkSize;
			}
			temp--;
	
	}	
	temp = 0;

	
	free(line);
	free(tempstr);
	free(searchstring);	
	free(String);
	
	/*determine number of files erased, direct them to the corresponding function*/
	if(filesUnavailable>(n-k)){
		printf("Error: Data Permanently Lost\n");
		exit(0);
		}
	else if(filesUnavailable == 1){
		printf("Data needs to be Recovered from surviving data files\n");
		Repair();
		}
	
	else if((filesUnavailable > 1)&&(filesUnavailable <=(n-k))){
		printf("Data has to be Recovered by downloading complete data object\n");
		Recover();
		exit(0);
		}
		
	else    
	printf("All Data nodes are Healthy, proceeding to decode data\n");			
		
		
return 0;
}




