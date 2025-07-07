#!/bin/bash
logfile=log.txt
_msg_hdr=LOG
error_detected=0
trap_msg=""

[ -f $logfile ] && rm -rf $logfile

function fatal () {
    printf "ERROR %s: %s\n" "${_msg_hdr}" "$*" >&2
    exit 1
}

function msg () {
     printf "%s: %s\n" "${_msg_hdr}" "$@"
     printf '\n--------\n%s: %s\n--------\n' "${_msg_hdr}" "$@" >> $logfile
}

function logcmd () {
    echo Exec: $@
    echo "++++++++" >> $logfile
    echo $@ >> $logfile
    echo "++++++++" >> $logfile

    eval "$@" >> $logfile 2>&1
    return $?
}

function chk_file (){
    local f=$1
    [ -e "$f" ] || fatal "file : $f is not found"
}

