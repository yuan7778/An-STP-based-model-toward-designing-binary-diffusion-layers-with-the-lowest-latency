import subprocess
import multiprocessing
import time
from datetime import datetime

PARAMS = [8,9,10,11,12]

def worker(p):

    start = time.time()

    logfile = f"log_{p}.txt"

    with open(logfile,"w") as log:

        log.write(f"Start : {datetime.now()}\n")
        log.write(f"Parameter = {p}\n\n")

       
        subprocess.run(
            ["python3","generate.py",str(p)],
            stdout=log,
            stderr=log
        )

     
        subprocess.run(
            ["stp",f"12_{p}.cvc"],
            stdout=log,
            stderr=log
        )

        end = time.time()

        log.write("\n")
        log.write(f"Runtime = {end-start:.2f} seconds\n")
        log.write(f"End = {datetime.now()}\n")

if __name__ == "__main__":

    pool = multiprocessing.Pool(processes=5)

    pool.map(worker, PARAMS)

    pool.close()
    pool.join()