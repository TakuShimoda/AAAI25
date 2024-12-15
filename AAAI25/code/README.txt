##README

## Execution Environment
- **Operating System**: Linux

## Compilation
To compile each program, use the following command:
g++ -std=c++17 -O3 "program.cc" -pthread -o program

##Execution
To run the program, use the following command: 
./program < "sas_file"

##Option
・The number of threads for parallelization (GBFS is a version of KPGBFS with thread_num=1)
You can specify the number of threads by changing the value of X in the following line (found around line 30 in the source code):
const int thread_num = X;

・Time limit (Seconds) 
You can specify the searching time limit by changing the value of X in the following line (found around line 35 in the source code):
const double time_limit = X;