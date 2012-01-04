/*SRC_files/SRC_decoder.c    
* Sarabjot Singh Khangura

SRC_decoder - A C/C++ application for decoding SRC (Simple Regenerating Code) encoded files
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
This program decodes SRC encoded files when all encoded files are available or when we lose upto (n-k) files.
   a. When there is no encoded file erasure, it simply locates the chunks in the files that have systematic data segments and writes them to file	
   b. if there are encoded file erasures, it would select any 'k' encoded files out of the available encoded files and thereon, uses Decode_by_reed_sol() function to decode.  
   Usage:'SRC_decoder <name of the file that was encoded using SRC>'
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


/*file pointer for metafile*/
FILE *meta;

/*file pointer for reading from coded files*/
FILE *ReadFileStreams;

/*variable to keep account of the files lost*/
int filesUnavailable = 0;

/*names of the files lost*/
char **fileNamesUnavailable;

/*indices of the files lost*/
int *nodeIndexUnavailable;

/*code parameters*/
int n,k,f,w,packetsize,m,buffersize;

/*variable for storing chunksize used in SRC*/                          	
long chunkSize = 0;
						 
/*string for storing line read from metafile*/
char *String;
							 
/*stores the name of the files to read from*/
char **file2beread;

/*variable to store number of read system calls to be made*/
int readins;
int size = 0;

/*stores the name of the file produced by decoding the encoded files*/
char *decodedName; 						

/*variable to keep account of the data written by each stream */
int *bytesEachDataStreamWrites2File;

/*file pointer for writing decoded data */
FILE **filedecoded;
FILE **readFileStreams;

// timing variables
double mem_time,total_mem_time;
// timing variables


/*structure to store information about chunk: index*/
typedef struct {
int fileIndex; 
long start;
long Nbytes;
} chunkInfoType;

typedef struct {
chunkInfoType chunkInfo;
} lookupTable;

/*look up table to store information about placement of chunks in encoded files */
lookupTable **LookupTable;

/*decoder that decoded using only 'k' SRC encoded files */
void Decode_by_reed_sol(){

	int *encoder_matrix;
	int *total;
	int temp_size;
	lookupTable *repairChunksTable,*nodePacketData;
	char **data,**coding;
	int *node2ReadFrom;
	int *erasedNodes,*erasure;
	int *erasedArray,*erasedstream;
	int bytesWritten2File;
	int i,j,p;
	int extra,q,z,decodeFlag;
	int index;
	int nodeSurviving;
	struct timeval start_mem_time, stop_mem_time;
	struct timezone tz;
	double total_mem_time;

	m = n-k;
	encoder_matrix = NULL;
	total_mem_time =0.0;	
	encoder_matrix = reed_sol_vandermonde_coding_matrix(k, m, w);

	
	total = (int*)malloc(sizeof(int)*n);		
	bytesEachDataStreamWrites2File = (int*)malloc(sizeof(int)*k*f);
	repairChunksTable = (lookupTable *)malloc(sizeof(lookupTable)*(f)*(f+1));
	data = (char**)malloc(sizeof(char*)*k);
	coding = (char**)malloc(sizeof(char*)*m);	
		
	nodePacketData = (lookupTable*)malloc(sizeof(lookupTable)*(f+1)*k);
	repairChunksTable = (lookupTable*)malloc(sizeof(lookupTable)*(f)*filesUnavailable);	
	
				
	//printf("Lost Files are :\n");	
	//for(i=0;i<filesUnavailable;i++)
	//	printf("%d. %s\n",i,fileNamesUnavailable[i]);
	
	node2ReadFrom = (int*)malloc(sizeof(int)*(k));
	erasedNodes = (int*)malloc(sizeof(int)*filesUnavailable);
	erasure = (int*)malloc(sizeof(int)*(n-k+1));
	erasedstream = (int*)malloc(sizeof(int)*(n-k+1));
	erasedArray = 	(int*)malloc(sizeof(int)*(n));
	
	temp_size = size;
	for(i=0;i<k*f;i++){
		if(temp_size>chunkSize){
		bytesEachDataStreamWrites2File[i] = chunkSize;
		temp_size = temp_size - chunkSize;
		}
		else if((temp_size < chunkSize)&&(temp_size != 0)){
			bytesEachDataStreamWrites2File[i] = temp_size;
			temp_size = 0;
		}
		else if(temp_size == 0){
			bytesEachDataStreamWrites2File[i] = 0;
		}
	}
	
	
	for(i=0;i<n;i++)
		erasedArray[i] = -1;
	// find files lost(or files lost)
	
	j=0;
	for(i=0;i<n;i++){
		if((nodeIndexUnavailable[i] == 1)){
			erasedNodes[j] = i;
			j++;	
		}
	}
	// -1 indicates available and 1 indicates lost	
	
	// pick any k files to read from and assume rest to be erased
	j=0;
	p=0;
	for(i=0;i<n;i++){
		if((nodeIndexUnavailable[i] == -1)&&(j<k)){
			node2ReadFrom[j] = i;
			j++;	
		}
		else{
			erasure[p] = i;
			erasedstream[p] = i;
			p++;
		}
	}
	erasure[p] = -1;
	erasedstream[p] = -1; 
	j=0;
	nodeSurviving = 0;
	for(j=0;j<k;j++){
		for(i = nodeSurviving;i<n;i++){
			if(nodeIndexUnavailable[i] == -1){
				nodeSurviving = i;
				break;
			}
		}		
	 
		for(i=0;i<(f+1);i++){
			(nodePacketData[i + j*(f+1)].chunkInfo).fileIndex = ((LookupTable[i+nodeSurviving*(f+1)])->chunkInfo).fileIndex;
			(nodePacketData[i+ j*(f+1)].chunkInfo).start = ((LookupTable[i+nodeSurviving*(f+1)])->chunkInfo).start;		
			((nodePacketData[i + j*(f+1)].chunkInfo).Nbytes =((LookupTable[i+nodeSurviving*(f+1)])->chunkInfo).Nbytes);
		}
		nodeSurviving = nodeSurviving + 1;		
	}
	
			
	/*determine number of read-ins */
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
	
	readFileStreams = (FILE**)malloc(sizeof(FILE*)*k);
	filedecoded = (FILE**)malloc(sizeof(FILE*));
	
	for(i=0;i<k;i++){
		if((readFileStreams[i] = fopen(file2beread[node2ReadFrom[i]],"rb")) == NULL)		
			printf("Unable to read file \n");
			}
	filedecoded[0] = fopen(decodedName,"wb");
		
			
	/*pick any 'k' files to be used for decoding*/		
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
				fseek(readFileStreams[j],i*chunkSize+(p-1)*buffersize,SEEK_SET);
						
				if((nodePacketData[i + j*(f+1)].chunkInfo).fileIndex < k){
					index = (nodePacketData[i + j*(f+1)].chunkInfo).fileIndex;
					erasedArray[index] = 1;
					if (total[index] < chunkSize && total[index]+buffersize <= chunkSize) {
							total[index] += fread(data[index], sizeof(char), buffersize,readFileStreams[j]);
							fflush(readFileStreams[j]);
						}
						else if (total[index] < chunkSize && total[index]+chunkSize > chunkSize) {
							extra = fread(data[index], sizeof(char), buffersize, readFileStreams[j]);
							fflush(readFileStreams[j]);
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
							total[index+k] += fread(coding[index], sizeof(char), buffersize,readFileStreams[j]);
							fflush(readFileStreams[j]);
						}
						else if (total[index+k] < chunkSize && total[index+k]+chunkSize > chunkSize) {
							extra = fread(coding[index], sizeof(char), buffersize, readFileStreams[j]);
							fflush(readFileStreams[j]);
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
			z=0;
			for(j=0;j<n;j++){
				if(erasedArray[j] == -1){
					erasedstream[z] = j;
					z++;
				}
			}
			erasedstream[z] = -1;
			z = 0;
					
				gettimeofday(&start_mem_time, &tz);	
			if((decodeFlag = jerasure_matrix_decode(k, m, w, encoder_matrix, 1, erasedstream, data, coding, buffersize))==-1){
				printf("Decoding Failed\n");
				exit(0);
			}
				gettimeofday(&stop_mem_time, &tz);
				mem_time = 0.0;
				mem_time += stop_mem_time.tv_usec;
				mem_time -= start_mem_time.tv_usec;
				mem_time /= 1000000.0;
				mem_time += stop_mem_time.tv_sec;
				mem_time -= start_mem_time.tv_sec;
				total_mem_time += mem_time;
			for(j=0;j<n;j++)
				erasedArray[j] = -1;
			
			for(j=0;j<k;j++){				
				if(bytesEachDataStreamWrites2File[i*k+j]>0){
					fseek(filedecoded[0],(i*k+j)*chunkSize+(p-1)*buffersize,SEEK_SET);
					if (bytesEachDataStreamWrites2File[i*k+j] >= buffersize) {
						bytesEachDataStreamWrites2File[i*k+j] -= fwrite(data[j], sizeof(char), buffersize,filedecoded[0]);
						bytesWritten2File += buffersize;
						fflush(filedecoded[0]);
					}
				else if (bytesEachDataStreamWrites2File[i*k+j] < buffersize) {
					for(q=0;q<(bytesEachDataStreamWrites2File[i*k+j]);q++){
							fprintf(filedecoded[0],"%c",data[j][q]);
							}
							bytesWritten2File = bytesWritten2File + q;
							bytesEachDataStreamWrites2File[i*k+j] -= q;
						if(bytesWritten2File == size)	 	
							break;
						
						}
					}					
				}
			p++;
			if(bytesWritten2File == size)	 	
				break;
		}
		for(j=0;j<k;j++)
			free(data[j]);
		for(j=0;j<m;j++)
			free(coding[j]);	
		if(bytesWritten2File == size)	 	
				break;		
	}
	fclose(filedecoded[0]);
	for(i=0;i<k;i++)
		fclose(readFileStreams[i]);
	
	printf("Decoding Rate (file size /totaltime) is %0.10f\n",(((float)size/1024)/1024)/(total_mem_time));	
} 



int main(int argc, char **argv){

	/*stores name of the files*/
	char *fname,*s1,*s2,*curdir;
	char *metafilename;
	

	/*loop variables*/
	int i,j,temp,q,extra;
	int p;
	
	/*file pointer for file produced by decoding encoded files*/
	FILE *decodedFile;
	
	/*buffer to store data read from the files */
	char *dataBuffer;
	
	/*keep account of the data read/written from/to the file*/
	int total,bytesWritten2File;
	
	/*variable to store strings read from the metafile*/
	char *searchstring,*tempstr,*line;
	int totalWrites = 0; 				
	
	/*timing variables*/
	struct timeval t1,t2;
	struct timezone tz;
	double totalsec,tsec;
	struct timeval start, stop;
	
	// starting the timer
	gettimeofday(&t1, &tz);
	totalsec = 0.0;
	


	if (argc != 2) {
			fprintf(stderr,  "usage: inputfile\n");
			exit(0);
		}
		
		
	/*find the current working directory*/
	curdir = (char*)malloc(sizeof(char)*1000);
	getcwd(curdir, 1000);
	
	/*create name for the decoded file*/
	decodedName = (char*)malloc(sizeof(char)*(strlen(curdir)+strlen(argv[1])+20));
	sprintf(decodedName,"%s/Coding/%s",curdir,argv[1]);		
	
	
	fname = (char*)malloc((sizeof(char)*(strlen(argv[1])+strlen(curdir)+10)));	
	s1 = (char*)malloc(sizeof(char)*(strlen(argv[1])+20));
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
		s2 = (char*)malloc(sizeof(char)*(strlen(argv[1])+10));
		if (fname != NULL) {
			strcpy(s2, fname);
		}	
	
	/*open meta file to read*/
	metafilename=(char*)malloc(sizeof(char)*(strlen(argv[1])+strlen("Coding")+strlen(s1)+strlen("_metanames.txt")+10+strlen(curdir)));
	sprintf(metafilename,"%s/Coding/%s_metanames.txt",curdir,s1);
	if((meta = fopen(metafilename,"r"))==NULL){
		printf("No Meta file Present");
		exit(0);
	}
		
	/*array to store strings read from the metafile*/
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
		file2beread = (char **)malloc(sizeof(char*)*n);
		nodeIndexUnavailable = (int *)malloc(sizeof(int)*n);
			
		/*find out the name of the file storing the encoded data*/
		temp = 0;
		for(i=0;i<n;i++){
			while ((fgets (line,500, meta))!=NULL ) {
				char *p;
				sprintf(tempstr,"data_%d%s",i,s2);
				sprintf(searchstring,line);
				p=strstr(searchstring,"\n");
				if(p!=NULL)
				*p = '\0';
				if((strstr(searchstring,tempstr)!=NULL)&&(strstr(searchstring,"=")==NULL))
				{
					file2beread[i] = (char *)malloc(sizeof(char)*strlen(searchstring)+1);
					strcpy(file2beread[i],searchstring);		
					
				}
			
								
			}
			fseek(meta, 0 ,SEEK_SET);
		}
		fclose(meta);
	temp = 0;
	fileNamesUnavailable = (char **)malloc(sizeof(char*)*n);
	
	/*search for the files lost*/
	for(i=0;i<n;i++){
		if((ReadFileStreams = fopen(file2beread[i],"rb")) == NULL){			
			filesUnavailable++;
			nodeIndexUnavailable[i] = 1;
			fileNamesUnavailable[filesUnavailable-1] = file2beread[i];
			
		}
		else {
			fclose(ReadFileStreams);
			nodeIndexUnavailable[i] = -1;
		}	
	}	
	
		
	temp = 0;
	LookupTable = (lookupTable**)malloc(sizeof(lookupTable*)*(n)*(f+1));
	for(i=0;i<(n)*(f+1);i++)
		LookupTable[i] = (lookupTable*)malloc(sizeof(lookupTable));
	
	
	
	/*generate a lookup table*/
	temp = n;
	for(i = 0; i<f+1; i++){
		for(j=0;(j<n);j++){
			(LookupTable[i+(f+1)*j]->chunkInfo).fileIndex = (j+temp) % n;
			(LookupTable[i+(f+1)*j]->chunkInfo).Nbytes = chunkSize;
			(LookupTable[i+(f+1)*j]->chunkInfo).start = i*chunkSize;
			}
			temp--;
	
	}
	
	if(filesUnavailable != 0){
		Decode_by_reed_sol();
		
		exit(0);	
	}
	
	
	/*determine the number of read system calls for each chunk */	
	temp = 0;
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
	
	
	bytesWritten2File = 0;
	dataBuffer = (char*)malloc(sizeof(char)*buffersize);
	decodedFile = fopen(decodedName,"ab");
		
	/*read from the file and simultaneously write to the decoded file*/
	temp = 0;	
	for(i=0;i<f;i++){
		temp = 0;
		for(temp=0;temp<k;temp++){	
			for(j=0;j<n;j++){
				if((LookupTable[i+(f+1)*j]->chunkInfo).fileIndex == temp){
				ReadFileStreams = fopen(file2beread[j],"rb");
				
				/*read from the files*/
				total = 0;
				totalWrites = 0;			
				p=1;
				while(p<=readins){
					fseek(ReadFileStreams,(LookupTable[i+(f+1)*j]->chunkInfo).start+(p-1)*buffersize,SEEK_SET);
					if (total < chunkSize && total+buffersize <= chunkSize) {
								total += fread(dataBuffer, sizeof(char), buffersize,ReadFileStreams);
								fflush(ReadFileStreams);
							}
							else if (total < chunkSize && total+buffersize > chunkSize) {			
								extra = fread(dataBuffer, sizeof(char), buffersize, ReadFileStreams);
								fflush(ReadFileStreams);
								for (q = extra; q < buffersize; q++) {
									dataBuffer[q] = '0';
								}
							}
							else if (total == chunkSize) {							
								for (q = 0; q < buffersize; q++) {					
									dataBuffer[q] = '0';
								}
							}
			
					fseek(decodedFile,(i*k+(LookupTable[i+(f+1)*j]->chunkInfo).fileIndex)*chunkSize+(p-1)*buffersize,SEEK_SET);
					p++;
					/*write to file*/
					if (bytesWritten2File < size && bytesWritten2File+buffersize <= size) {
								bytesWritten2File += fwrite(dataBuffer, sizeof(char), buffersize,decodedFile);
								fflush(decodedFile);
							}
						else if (bytesWritten2File < size && bytesWritten2File+buffersize > size) {
							for(q=0;q<(size-bytesWritten2File);q++){
									fprintf(decodedFile,"%c",dataBuffer[q]);
									}
									bytesWritten2File = bytesWritten2File + q;
								break;	
								}		
							
											
					}
					fclose(ReadFileStreams);
					/*if we have written to the file data equal to the size of the file that was encoded, stop the process*/
					if(bytesWritten2File == size)
					break;	
				}
				if(bytesWritten2File == size)
					break;
			}
			if(bytesWritten2File == size)
					break;
		}
		if(bytesWritten2File == size)
					break;	
	}

	 gettimeofday(&t2, &tz);
	tsec = 0.0;
	tsec += t2.tv_usec;
	tsec -= t1.tv_usec;
	tsec /= 1000000.0;
	tsec += t2.tv_sec;
	tsec -= t1.tv_sec;
	totalsec += tsec;
	//Calculating Encoding rate
	printf("Time taken to decode file  total size %d is %0.10f\n",size,totalsec);
	printf("Decode Rate (file size /totaltime) is %0.10f\n",(((float)size/1024)/1024)/(totalsec));	
		
			



}
