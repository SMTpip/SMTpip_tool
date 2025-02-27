import os
import json
import time
import pandas as pd
import numpy as np
import nltk

# Download NLTK data (if not already downloaded)
nltk.download('punkt')

def load_json_data(filepath):
    if os.path.exists(filepath):
        with open(filepath, 'r') as file:
            return json.load(file)
    else:
        print(f"File {filepath} not found.")
        return None

def process_text(text):
    words = nltk.word_tokenize(text)
    return words

def text_analysis(articles):
    results = []
    for article in articles:
        word_count = len(process_text(article['content']))
        results.append({
            'id': article['id'],
            'title': article['title'],
            'word_count': word_count
        })
    return pd.DataFrame(results)

def main():
    start_time = time.time()
    
    # Load the data
    filepath = os.path.join("data", "sample_text.json")
    data = load_json_data(filepath)
    
    if data:
        # Analyze the articles
        df = text_analysis(data['articles'])
        
        # Some basic analysis using pandas and numpy
        avg_word_count = np.mean(df['word_count'])
        print(f"Average word count: {avg_word_count}")
        
        # Display the dataframe
        print(df)

    end_time = time.time()
    print(f"Processing completed in {end_time - start_time:.2f} seconds.")

if __name__ == "__main__":
    main()
