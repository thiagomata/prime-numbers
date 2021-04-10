import pandas as pd
import matplotlib.pyplot as plt

import glob

csvFiles = glob.glob('*.csv')

for csvFile in csvFiles:
    print(csvFile)
    df= pd.read_csv(csvFile ,index_col=0)
    plt.clf()
    plt.imshow(df,cmap='hot',interpolation='gaussian')
    plt.colorbar()
    plt.savefig(csvFile[:-4] + ".png", dpi = 1000)
