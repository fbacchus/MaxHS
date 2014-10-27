MaxHS---a maxsat solver expoiting a hybrid approach between SAT and
MIPS. The code uses minisat as the SAT solver and CPLEX from IBM as
the MIPS solver. The Makefile setup is a modification of the minisat
Makefile. 

MaxHS was created by Jessica Davies and Fahiem Bacchus.

For further information see

www.maxhs.org

---------------------------------------------------------------------

Building and installing:
-----------------------
0) Get CPLEX. 
-------------
   You need the CPLEX static libraries to link against. CPLEX is
   available from IBM under their academic Initiative program. It is
   free to faculty members and graduate students in academia. 

   try 
   http://www-03.ibm.com/ibm/university/academic/pub/page/ban_ilog_programming

   a google search should find the right site.
   You apply for their academic initiative program and then then you
   can download CPLEX and other IBM software. 

   Note. CPLEX is very useful for many tasks and well worth having
   access to irrespective of MaxHS. 


1) Configure
------------
Use "make config VAR=defn" or edit config.mk directly. 

REQUIRED VARIABLE SETTINGS:
===========================

CPLEXLIBDIR=<path to CPLEX library>
   #the directory should contain libcplex.a and libilocplex.a as
   #currently we do a static build.
CONCERTLIBDIR=<path to concert library>
   #should contain libconcert.a
CPLEXINCDIR=<path to CPLEX headers>
CONCERTINCDIR=<path to CONCERT headers>

RECOMMENDED VARIABLE SETTINGS:
==============================

prefix=<location for install; default = '/usr/local'>
  #Root install directory for GNU standard install locations 
  #finer control can be achieved by modifying the GNU install
  #variables (e.g., includedir, bindir, etc). See the Makefile
  #"make install" will put the executable in $(prefix)/bin


OPTIONAL VARIABLE SETTINGS:
==========================

Various compiler settings can be configured, see the Makefile

Notes:

- Multiple configuration steps can be joined into one call to "make
  config" by appending multiple variable assignments on the same line.

- The configuration is stored in the file "config.mk". Look here if
  you want to know what the current configuration looks like.

- To reset from defaults simply remove the "config.mk" file or call
  "make distclean".

- Once configured, recompilation can be done as many times as wanted. 

2) Compile and Build 
-----------

make install

================================================================================
Directory Overview:

maxhs/                  MaxHs code
minisat/mtl/            Minsat  Template Library
minisat/utils/          Minisat helper code (I/O, Parsing, CPU-time, etc)
minisat/core/           Minisat core solver (does not do simplification)
README
LICENSE

================================================================================

