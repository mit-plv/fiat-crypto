@echo off
if not defined in_subprocess (cmd /k set in_subprocess=y ^& %0 %*) & exit

SET "SCRIPT_DIR=%~dp0"

ECHO ::group::wmic cpu get caption, deviceid, name, numberofcores, maxclockspeed, status
wmic cpu get caption, deviceid, name, numberofcores, maxclockspeed, status &
ECHO ::endgroup::
ECHO ::group::wmic cpu list /format:list
wmic cpu list /format:list &
ECHO ::endgroup::
ECHO ::group::git config -l
%CYGWIN_ROOT%\bin\bash.exe -l -c 'git config -l' &
ECHO ::endgroup::
ECHO ::group::git config --global -l
%CYGWIN_ROOT%\bin\bash.exe -l -c 'git config --global -l' &
ECHO ::endgroup::
ECHO ::group::opam list
opam list &
ECHO ::endgroup::
ECHO ::group::ocamlc -config
opam exec -- ocamlc -config &
ECHO ::endgroup::
ECHO ::group::coqc --config
opam exec -- coqc --config &
ECHO ::endgroup::
ECHO ::group::coqc --version
opam exec -- coqc --version &
ECHO ::endgroup::
ECHO ::group::coqtop version
opam exec -- coqtop <nul &
ECHO ::endgroup::
ECHO ::group::make printenv
%CYGWIN_ROOT%\bin\bash.exe -l -c 'cd "%cd%"; opam exec -- make printenv' &
ECHO ::endgroup::
ECHO ::group::PATH
%CYGWIN_ROOT%\bin\bash.exe -l -c 'cd "%cd%"; echo "${PATH}"' &
ECHO ::endgroup::

powershell -ExecutionPolicy Bypass -File "%SCRIPT_DIR%github-actions-record-coq-info.ps1"
