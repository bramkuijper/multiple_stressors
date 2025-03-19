#!/usr/bin/env Rscript

autocorr0 <- c(0,0.1,0.5,0.9)
risk0 <- c(0.1,0.5,0.9)
autocorr1<- c(0,0.1,0.5,0.9)
risk1<- c(0.1,0.5,0.9)

pAttack <- c(0.5,0.5)

repair <- 20

file_contents <- ""

timestamp_string <- format(Sys.time(), "%Y%m%d_%H%M%S")

job_counter <- 0

executable = "./stress_nstressors.exe"

for (autocorr0_i in autocorr0)
{
    for (risk0_i in risk0)
    {
        for (autocorr1_i in autocorr1)
        {
            for (risk1_i in risk1)
            {
                job_counter <- job_counter + 1
                file_base_name <- paste0("stress_",timestamp_string,"_",job_counter)

                job_line <- paste0(executable, " ",
                                    autocorr0_i, " ",
                                    autocorr1_i, " ",
                                    risk0_i, " ",
                                    risk1_i, " ",
                                    repair, " ",
                                    job_counter, " ",
                                    pAttack[1], " ",
                                    pAttack[2], " ",
                                    file_base_name
                                    )

                file_contents <- paste0(file_contents, "\n", job_line)
            }
        }
    }
}

writeLines(text = file_contents)
