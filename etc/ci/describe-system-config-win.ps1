# Set the script directory variable
$SCRIPT_DIR = Split-Path -Parent -Path $MyInvocation.MyCommand.Definition

# Function to print groups for better readability in logs
function Print-Group {
    param ($name, $command)
    Write-Host "::group::$name"
    & $command -ErrorAction Continue
    Write-Host "::endgroup::"
}

# Using WMI to get CPU information
Print-Group -name "wmic cpu get" -command { Get-CimInstance -ClassName CIM_Processor | Select Caption, DeviceID, Name, NumberOfCores, MaxClockSpeed, Status }
Print-Group -name "wmic cpu list /format:list" -command { wmic cpu list /format:list }

# Running git configuration commands via bash
$CYGWIN_ROOT = $env:CYGWIN_ROOT
Print-Group -name "git config -l" -command { & "$CYGWIN_ROOT\bin\bash.exe" -l -c 'git config -l' }
Print-Group -name "git config --global -l" -command { & "$CYGWIN_ROOT\bin\bash.exe" -l -c 'git config --global -l' }

# Using opam and OCaml tools
Print-Group -name "opam list" -command { opam list }
Print-Group -name "ocamlc -config" -command { opam exec -- ocamlc -config }
Print-Group -name "coqc --config" -command { opam exec -- coqc --config }
Print-Group -name "coqc --version" -command { opam exec -- coqc --version }
Print-Group -name "coqtop version" -command { "" | opam exec -- coqtop }

# gcc
Print-Group -name "gcc -v" -command { opam exec -- gcc -v }
Print-Group -name "gcc --version" -command { opam exec -- gcc --version }
Print-Group -name "ldd --version" -command { opam exec -- ldd --version }

# Using make with environmental variables
Print-Group -name "make printenv" -command { opam exec -- make printenv }
Print-Group -name "PATH=$PATH" -command { & "$CYGWIN_ROOT\bin\bash.exe" -l -c 'echo "${PATH}"' }

Print-Group -name "Writing info to '$env:GITHUB_STEP_SUMMARY'" -command { & PowerShell.exe -ExecutionPolicy Bypass -File "$SCRIPT_DIR\github-actions-record-coq-info.ps1" }
