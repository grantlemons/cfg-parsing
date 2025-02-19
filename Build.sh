#!/bin/sh

# 1. Set PROJECT in this Build.sh file to the name of the course project (SIM,
#    NFAMATCH, ...).  CSCI423 (Simulation) students should already see it as
#    SIM.  Be sure your main .rs source file the lowercase version of
#    PROGRAM.
# 2. ZIP up your Cargo.toml and src/ directory alongside this modified Build.sh, test
#    on alamode (https://cs.mcprogramming.com/comp/Assignments/SubmitOnDjComp)
# 3. Be sure to NOT SUBMIT the Cargo.lock file, PROGRAM file or ./target directory
#    (as per Assignments/Requirements).

PROJECT=ALPHABETENCODING
project=`echo ${PROJECT}|tr A-Z a-z`

# you are welcome to change the rust invocation, but this might alter the path
# required for the last ln(1) command in the script
cargo build --${PROFILE:-release} --bin ${project}

# purge, just in case it is a directory for some bizarre reason.
rm -rf ${PROJECT}

# move the executable resident under target/.../ back to the top directory, where
# project requirements expect it to be.
ln -s target/${PROFILE:-release}/${project} ./${PROJECT}
