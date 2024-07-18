from flask import Flask
from threading import Thread
import logging



app = Flask('')

log = logging.getLogger('werkzeug')
log.setLevel(logging.ERROR)

@app.route('/')

def home():
    return f"<h1>😎I'm Awake Already!🔥</h1>"

def run():
  app.run(host='0.0.0.0',port=7860)



def keep_alive():
    t = Thread(target=run)
    t.start()