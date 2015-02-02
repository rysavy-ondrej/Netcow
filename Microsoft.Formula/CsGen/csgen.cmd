@echo off
setlocal EnableDelayedExpansion

set inputs=%~1
set outputs=%~2

REM set inputs=%inputs:~1,-1%
REM set outputs=%outputs:~1,-1%

echo INPUTS: %inputs%
echo OUTPUTS: %outputs%

set i=0
for %%x in (%inputs%) do (
   set inarr[!i!]=%%x
   REM echo IN=!i! VAL=%%x
   set /A i+=1
)

set i=0
for %%x in (%outputs%) do (
   set outarr[!i!]=%%x
   REM echo OUT=!i! VAL=%%x
   set /A i+=1
)

set myarr[0]=Foo
set myarr[1]=Bar
set myarr[2]=Xtr

call:array_len inarr arrlen
REM echo LENGTH=%arrlen%
for /L %%x in (0,1,%arrlen%) do (
  call:array_getitem inarr %%x infile
  call:array_getitem outarr %%x outfile
  "%~dp0\formula.csgen.exe" "!infile!" "!outfile!"
)

goto:eof

REM Example call: call :getitem myarray 1 value
REM After that: 'echo %value%' outputs in this case "lights"
:array_getitem
SETLOCAL
set array.name=%~1
set array.index=%~2
set outputvar=nofile
for /f "delims=[]= tokens=1,2,3" %%a in ('set %array.name%') do (
  if %%b==%array.index% set outputvar=%%c
)
ENDLOCAL & ( set "%3=%outputvar%" )
goto:eof
:array_len
REM Gets array length.
REM Arguments: (
REM name As "Array name"
REM var As "Output Variable"
REM )
set array.name=%1
set array.var=%2
for /f "delims=[=] tokens=2" %%a in ('set %array.name%[') do (
set %array.var%=%%a
)
goto :eof


		 